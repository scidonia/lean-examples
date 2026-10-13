#!/usr/bin/env python3
"""Check that every frame in the paper still quotes what it claims.

Five kinds of check, all against the library:

  a frame command
  \\codeframe[linerange=<lo>-<hi>]{<file>}
  \\lawframe{<file>}{<lo>-<hi>}{<name>}
      every occurrence of either command must be one of those two calls, with a
      numeric `lo-hi` range.  Recognition is total (`framescan.py`): a missing
      bracket, path or brace, a range that is not a numeric `lo-hi`, and a
      placeholder outside the two macro definitions are reported, so a call the
      paper makes cannot pass as a form no pattern happens to match;

  %!check: <fragment>
  \\codeframe[linerange=<lo>-<hi>]{<file>}
      the quoted range must contain <fragment>, so a range that still has the
      right shape but has moved off its declaration fails;

  \\lawframe{<file>}{<lo>-<hi>}{<name>}
      the range must contain the declaration of <name>;

  frames/<key>.lean
      the generated frame must be exactly the range with its comments removed,
      by leanstrip.py, recomputed here.  This is what makes a frame's content
      checked rather than asserted: the generator writes the file, and this
      recomputes it.  A range whose code strips to nothing is a failure rather
      than an empty frame an empty file could match.

  counts.tex
      the generated counts must be exactly what gen-laws.py derives from the
      library and from the paper's own call sites, recomputed here.  This is
      what keeps a stated number -- the theorems the library publishes, the
      panels the paper quotes -- from outliving what it counts.

Usage:  python3 check-listings.py [file.tex ...]      # default: every *.tex here,
                                                      # and then the self-test
        python3 check-listings.py --self-test         # the self-test alone
Exit status 0 when every frame and count checks out, 1 otherwise.

A source that cannot be opened, and a range the source does not reach, are
failures rather than skipped checks: both are reported and neither counts as a
check performed, so the summary cannot report a panel as checked when nothing
was read.

The default run is the one a reader runs, so it also runs the self-test: the
scratch paper that pins these checks, red, against each form of failure they
exist to catch.  A check whose red case has stopped failing is a check that has
stopped guarding, and the default run then fails too.  Naming files runs the
checks alone, which is what the self-test itself does.
"""

import importlib.util
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import framescan
import leanstrip

CHECK = re.compile(r"^\s*%\s*!check:\s*(?P<frag>.*\S)\s*$")
LOOKUP = re.compile(
    r"\\expandafter\\def\\csname cf@(?P<path>.*)@(?P<lo>\d+)-(?P<hi>\d+)"
    r"\\endcsname\{(?P<key>[^}]*)\}"
)
KINDS = "inductive|structure|class|abbrev|def|theorem|lemma"


def panel_text(path: str, lo: int, hi: int) -> str:
    """A panel call as the paper writes one, for a message."""
    return f"\\codeframe[linerange={lo}-{hi}]{{{path}}}"


def normalise(text: str) -> str:
    """Collapse runs of whitespace so that indentation does not matter."""
    return re.sub(r"\s+", " ", text).strip()


def read_source(path: Path, limit: int, context: str,
                problems: list[str]) -> list[str] | None:
    """The lines of `path`, or None after recording that it cannot be read.

    A source that cannot be opened and a range its file does not reach are both
    failures rather than skipped checks: each is recorded in `problems`, which is
    what the entrypoint fails on, and the caller counts the check only when this
    returns lines.
    """
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        problems.append(f"{context}: cannot read {path}: {error}")
        return None
    if limit > len(lines):
        problems.append(f"{context}: {path} has only {len(lines)} lines, "
                        f"range is ..{limit}")
        return None
    return lines


def check_fragments(tex: Path, calls: list, problems: list[str]) -> int:
    """Verify each %!check: directive against every frame that follows it.

    A line can carry more than one call, and each call is a panel: the directive
    before the line pairs with the first, and a second call on the same line has
    no directive of its own to pair with, so it is reported rather than passed
    over.  Only the calls `framescan` recognizes are panels, so a command the
    typesetter never reaches neither asks for a directive nor takes one, and a
    malformed one is reported by the caller rather than paired with anything.
    """
    lines = tex.read_text(encoding="utf-8").splitlines()
    panels: dict[int, list] = {}
    for kind, number, path, lo, hi, _ in calls:
        if kind == "codeframe":
            panels.setdefault(number, []).append((path, lo, hi))
    pending, checked = None, 0
    for number, line in enumerate(lines, start=1):
        match = CHECK.match(line)
        if match:
            if pending is not None:
                problems.append(
                    f"{tex.name}:{pending[0]}: %!check: with no frame between it "
                    f"and the one at line {number}")
            pending = (number, match.group("frag"))
            continue
        for path, lo, hi in panels.get(number, []):
            if pending is None:
                problems.append(f"{tex.name}:{number}: frame without a %!check: "
                                f"{panel_text(path, lo, hi)}")
                continue
            directive, fragment = pending
            pending = None
            where = f"{tex.name}:{directive}"
            body = read_source(tex.parent / path, hi, where, problems)
            if body is None:
                continue
            checked += 1
            if normalise(fragment) not in normalise("\n".join(body[lo - 1:hi])):
                problems.append(
                    f"{where}: {path}:{lo}-{hi} does not contain\n"
                    f"    {fragment}")
    if pending is not None:
        problems.append(f"{tex.name}:{pending[0]}: trailing %!check: with no frame")
    return checked


def check_lawframes(tex: Path, calls: list, problems: list[str]) -> int:
    """Verify each law frame against the declaration it names."""
    checked = 0
    for kind, number, module, lo, hi, name in calls:
        if kind != "lawframe":
            continue
        where = f"{tex.name}:{number}"
        name = name.replace("\\_", "_").replace("\\%", "%")
        body = read_source(tex.parent / ".." / module, hi, where, problems)
        if body is None:
            continue
        decl = re.compile(rf"^(?:@\[[^\]]*\]\s*)?(?:{KINDS})\s+{re.escape(name)}(?![\w'])")
        if not any(decl.match(line) for line in body[lo - 1:hi]):
            problems.append(
                f"{where}: no declaration of {name} in {module}:{lo}-{hi}\n"
                f"    first line: {body[lo - 1]!r}")
            continue
        checked += 1
    return checked


def load_lookup(here: Path, problems: list[str]) -> dict:
    """The generated table: (path, lo, hi) -> the frame's key."""
    table = {}
    try:
        text = (here / "frames/lookup.tex").read_text(encoding="utf-8")
    except OSError as error:
        problems.append(f"cannot read frames/lookup.tex: {error}\n"
                        f"    run python3 gen-frames.py")
        return table
    for match in LOOKUP.finditer(text):
        table[(match.group("path"), int(match.group("lo")), int(match.group("hi")))] = \
            match.group("key")
    return table


def check_frames(here: Path, tex: Path, table: dict, calls: list,
                 problems: list[str]) -> int:
    """Verify every generated frame against the range it was generated from."""
    checked = 0
    for kind, number, path, lo, hi, _ in calls:
        where = f"{tex.name}:{number}"
        if kind == "lawframe":
            path = "../" + path
        key = table.get((path, lo, hi))
        if key is None:
            problems.append(f"{where}: no generated frame for {path}:{lo}-{hi}\n"
                            f"    run python3 gen-frames.py")
            continue
        try:
            frame = (here / "frames" / f"{key}.lean").read_text(encoding="utf-8")
        except OSError as error:
            problems.append(f"{where}: cannot read frames/{key}.lean: {error}")
            continue
        source = (here / path).resolve()
        lines = read_source(source, hi, where, problems)
        if lines is None:
            continue
        want = leanstrip.frame_body(lines, lo, hi)
        if not want.strip():
            problems.append(f"{where}: {path}:{lo}-{hi} quotes no code")
            continue
        got = frame.rstrip("\n")
        if want != got:
            problem = (f"{where}: frames/{key}.lean is not comments-stripped "
                       f"{path}:{lo}-{hi}")
            for a, b in zip(want.splitlines(), got.splitlines()):
                if a != b:
                    problem += f"\n    source: {a!r}\n    frame:  {b!r}"
                    break
            else:
                problem += f"\n    {len(want.splitlines())} lines expected, "\
                           f"{len(got.splitlines())} held"
            problems.append(problem)
            continue
        checked += 1
    return checked


def load_generator(here: Path):
    """Load gen-laws.py, which derives the counts counts.tex holds.

    Its name has a hyphen, so it is loaded from its path rather than imported by
    name; loading it generates nothing, as its work is under a __main__ guard.
    """
    spec = importlib.util.spec_from_file_location("gen_laws", here / "gen-laws.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_counts(here: Path, problems: list[str]) -> int:
    """Verify counts.tex against the counts the library and the paper imply."""
    path = here / "counts.tex"
    try:
        held = path.read_text(encoding="utf-8")
    except OSError as error:
        problems.append(f"cannot read counts.tex: {error}\n"
                        f"    run python3 gen-laws.py")
        return 0
    want = load_generator(here).counts_text()
    if held.rstrip("\n") != want.rstrip("\n"):
        problem = "counts.tex is not the file gen-laws.py generates"
        for a, b in zip(want.splitlines(), held.splitlines()):
            if a != b:
                problem += f"\n    generated:  {a!r}\n    counts.tex: {b!r}"
                break
        else:
            problem += (f"\n    {len(want.splitlines())} lines generated, "
                        f"{len(held.splitlines())} held")
        problems.append(problem + "\n    run python3 gen-laws.py")
        return 0
    return 1


# The self-test's scratch archive: these scripts, the library gen-laws.py locates
# its counts in, one source to quote, and two papers.  Probe.lean is the source
# every case quotes: a declaration on its second and third lines and a doc
# comment on its first, so the one file gives a range that holds code, a range
# that strips to nothing, and a range its end does not reach.  The archive is a
# temporary copy, so neither run reads or writes the papers beside this script.
SELF_TEST_TREES = ("Scidonia", "ScidoniaTest")
SELF_TEST_SCRIPTS = ("check-listings.py", "gen-laws.py", "gen-frames.py",
                     "framescan.py", "leanstrip.py")
SELF_TEST_SOURCE = ("/-- A declaration to quote. -/\n"
                    "def probeValue : Nat :=\n"
                    "  41 + 1\n")
SELF_TEST_PANEL = "\\codeframe[linerange=2-3]{../Scidonia/Probe.lean}"
SELF_TEST_SECOND = "\\codeframe[linerange=3-3]{../Scidonia/Probe.lean}"
SELF_TEST_PAIRED = ("%!check: def probeValue\n" + SELF_TEST_PANEL + "\n"
                    "\n"
                    "%!check: 41 + 1\n" + SELF_TEST_SECOND + "\n")
SELF_TEST_SAME_LINE = ("%!check: def probeValue\n"
                       + SELF_TEST_PANEL + " " + SELF_TEST_SECOND + "\n")
# The counted paper's lines each carry two calls, one line above \appendix and
# one below it: two calls are two panels, on either side of the split, and a
# count of the lines they are written on would state half of that.
SELF_TEST_COUNTED = ("% A stand-in for a counted paper.\n"
                     + SELF_TEST_PANEL + " " + SELF_TEST_SECOND + "\n"
                     "\\appendix\n"
                     + SELF_TEST_PANEL + " " + SELF_TEST_SECOND + "\n")
SELF_TEST_PAIRED_SUMMARY = ("2 quoted panels, 0 law frames and 2 generated frames "
                            "checked, 1 generated counts checked, 0 failed")
SELF_TEST_UNPAIRED = "frame without a %!check: " + SELF_TEST_SECOND
SELF_TEST_PANELCOUNT = "\\newcommand{\\panelcount}{4}"
SELF_TEST_APPENDIXCOUNT = "\\newcommand{\\appendixpanelcount}{2}"
# Both papers' preambles define the two commands, and that parameter text is not
# a frame: a paper carrying the definitions beside a real panel must check out,
# or the recognition that catches a malformed call is also catching the macros.
SELF_TEST_TEMPLATES = (
    "\\def\\codeframe[linerange=#1-#2]#3{%\n"
    "  \\inputminted{lean}{frames/#3.lean}}\n"
    "\\newcommand{\\lawframe}[3]{%\n"
    "  \\texttt{#3} \\codeframe[linerange=#2]{../#1}}\n"
    "%!check: def probeValue\n"
    + SELF_TEST_PANEL + "\n")
# One case per form of failure these checks exist to catch, each a whole paper
# run through the scripts as the command line runs them.  A case is what the
# checker must report, and what the generator must for the forms it recognizes
# too (None means the generator has nothing to say and it is not run).  A case
# that stops reporting its diagnostic, or that passes where it must fail, is a
# case whose guard has stopped guarding, and the self-test records it.
SELF_TEST_RED = [
    ("a codeframe call with no closing brace",
     "%!check: def probeValue\n"
     "\\codeframe[linerange=2-3]{../Scidonia/Probe.lean\n",
     "malformed \\codeframe call: no {path} after [linerange=2-3]",
     "MALFORMED FRAME CALL"),
    ("a codeframe call with no closing bracket",
     "\\codeframe[linerange=2-3{../Scidonia/Probe.lean}\n",
     "malformed \\codeframe call: no [linerange=lo-hi]{path}",
     "MALFORMED FRAME CALL"),
    ("a lawframe call with no closing brace",
     "\\lawframe{Scidonia/FracPerm/Ledger.lean}{25-25}{held_nil\n",
     "malformed \\lawframe call: no {path}{lo-hi}{name}",
     "MALFORMED FRAME CALL"),
    ("a source that cannot be read",
     "%!check: def probeValue\n"
     "\\codeframe[linerange=2-3]{../Scidonia/Absent.lean}\n",
     "cannot read",
     "MISSING SOURCE"),
    ("a range past the end of its source",
     "%!check: def probeValue\n"
     "\\codeframe[linerange=2-9]{../Scidonia/Probe.lean}\n",
     "has only 3 lines, range is ..9",
     "RANGE PAST END"),
    ("a placeholder where a range belongs",
     "%!check: def probeValue\n"
     "\\codeframe[linerange=#1-#2]{../Scidonia/Probe.lean}\n",
     "\\codeframe[linerange=#1-#2] is not a numeric lo-hi range",
     "MALFORMED FRAME CALL"),
    ("a range that is not numeric",
     "%!check: def probeValue\n"
     "\\codeframe[linerange=2-x]{../Scidonia/Probe.lean}\n",
     "\\codeframe[linerange=2-x] is not a numeric lo-hi range",
     "MALFORMED FRAME CALL"),
    ("a range whose code strips to nothing",
     "%!check: /-- A declaration to quote. -/\n"
     "\\codeframe[linerange=1-1]{../Scidonia/Probe.lean}\n",
     "quotes no code",
     "EMPTY FRAMES"),
    ("a fragment its quoted range does not contain",
     "%!check: def probeValue\n"
     "\\codeframe[linerange=3-3]{../Scidonia/Probe.lean}\n",
     "does not contain",
     None),
    ("a directive superseded before its frame",
     "%!check: def probeValue\n"
     "%!check: 41 + 1\n"
     + SELF_TEST_PANEL + "\n",
     "%!check: with no frame between it and the one at line 2",
     None),
    ("a second call on a line, with no directive",
     SELF_TEST_SAME_LINE,
     SELF_TEST_UNPAIRED,
     None),
]
# A panel the generator has never seen: generate for a paper, then add a call.
SELF_TEST_UNFRAMED = SELF_TEST_PAIRED + (
    "%!check: def probeValue\n"
    "\\codeframe[linerange=2-2]{../Scidonia/Probe.lean}\n")
SELF_TEST_UNFRAMED_WANTED = "no generated frame for ../Scidonia/Probe.lean:2-2"


def indented(text: str) -> str:
    """A run's output, indented under the line that reports it."""
    return "".join("    " + line + "\n" for line in text.splitlines())


def in_archive(paper: Path, *args: str):
    """Run one of the archive's scripts in it, as the command line does.

    A run that cannot be launched -- no interpreter to launch it with, or
    nothing readable at the script's path -- has no status for a case to read,
    so it is given one: exit 127, the shell's status for a command that did not
    run, and a diagnostic naming what was to be run and why it did not.  A case
    whose script never started is then reported like any other failure, rather
    than passing for want of anything to check.
    """
    if not sys.executable:
        return subprocess.CompletedProcess(
            args, 127, "",
            "cannot run the archive's scripts: no interpreter in "
            "sys.executable\n")
    command = [sys.executable, *args]
    try:
        return subprocess.run(command, cwd=paper,
                              capture_output=True, text=True)
    except OSError as error:
        return subprocess.CompletedProcess(
            command, 127, "",
            f"cannot run {' '.join(args)} in {paper}: {error}\n")


def report_of(run) -> str:
    """A run's output, without the generator's per-frame listing.

    `gen-frames.py` prints one line per frame it writes, which is a page of
    lines beside the diagnostic a case is about.  That listing is indented under
    the run's report; the diagnostics and the summary are not.
    """
    return "\n".join(line for line in (run.stdout + run.stderr).splitlines()
                     if not line.startswith("  "))


def expect(case: str, run, must_fail: bool, wanted: str,
           problems: list[str]) -> None:
    """Record a problem unless `run` printed `wanted` and ended as it must."""
    print(f"--- {case}: exit {run.returncode}")
    print(indented(report_of(run)), end="")
    if wanted not in run.stdout + run.stderr:
        problems.append(f"{case}: did not report\n    {wanted}")
    if run.returncode == 0 and must_fail:
        problems.append(f"{case}: a paper it must reject passed")
    if run.returncode != 0 and not must_fail:
        problems.append(f"{case}: a paper it must accept did not check out")


def reported(problems: list[str]) -> int:
    """Report the self-test's problems, and its verdict, and fail for any.

    A problem is a failure, so it is printed on stderr as well as stdout: a
    reader of either stream, and a run whose output is piped past one of them,
    still sees what went wrong.  A run that could not reach the library, its
    scripts or its scratch archive reports that reason the same way and with the
    same non-zero status, so a run that checked nothing cannot be read as one
    that passed.  A self-test with no problems prints its verdict on stdout
    alone.
    """
    for problem in problems:
        print(problem)
        print(problem, file=sys.stderr)
    print(f"self-test: "
          f"{'failed' if problems else 'the scratch archive checked out'}")
    return 1 if problems else 0


def scratch_cases(here: Path, problems: list[str]) -> None:
    """Run every case against a scratch paper that is wrong in one place.

    The archive carries this checker, the generators, the recognizer and the
    library, so every case exercises the command line rather than a function
    inside it.  Each case is a paper written into the archive and run through
    the scripts as the command line runs them, and what it reports is recorded
    in `problems`: that is what makes each of these checks falsifiable rather
    than merely plausible.  A scratch tree that cannot be built or written
    leaves the failure to the caller, which reports it rather than passing the
    run off as one that checked something.
    """
    with tempfile.TemporaryDirectory(prefix="check-listings-") as temporary:
        root, paper = Path(temporary), Path(temporary) / "Paper"
        paper.mkdir()
        for script in SELF_TEST_SCRIPTS:
            shutil.copy2(here / script, paper / script)
        for tree in SELF_TEST_TREES:
            shutil.copytree(here.parent / tree, root / tree)
        (root / "Scidonia/Probe.lean").write_text(SELF_TEST_SOURCE,
                                                  encoding="utf-8")
        (paper / "lowering.tex").write_text("% No panels.\n", encoding="utf-8")
        (paper / "unobservable-effects.tex").write_text(SELF_TEST_COUNTED,
                                                        encoding="utf-8")
        (paper / "probe.tex").write_text(SELF_TEST_PAIRED, encoding="utf-8")
        for script in ("gen-laws.py", "gen-frames.py"):
            step = in_archive(paper, script)
            if step.returncode != 0:
                problems.append(f"{script} failed in the scratch archive:\n"
                                + step.stdout + step.stderr)

        # A paper whose every panel has the directive before it checks out, and
        # the paper the counts are taken from is counted in calls.
        paired = in_archive(paper, "check-listings.py", "probe.tex")
        expect("a directive before each panel", paired, False,
               SELF_TEST_PAIRED_SUMMARY, problems)
        if SELF_TEST_UNPAIRED in paired.stdout:
            problems.append("the paired paper reported " + SELF_TEST_UNPAIRED)
        counts = (paper / "counts.tex").read_text(encoding="utf-8")
        for wanted in (SELF_TEST_PANELCOUNT, SELF_TEST_APPENDIXCOUNT):
            if wanted not in counts:
                problems.append("two calls on one line are not counted as two "
                                "panels: counts.tex does not state\n    " + wanted)

        # The definitions' parameter text is a call to neither script, so the
        # paper that carries the definitions must check out.
        (paper / "probe.tex").write_text(SELF_TEST_TEMPLATES, encoding="utf-8")
        templates = in_archive(paper, "gen-frames.py")
        if templates.returncode != 0:
            problems.append("gen-frames.py failed on the paper with the "
                            "definitions:\n" + templates.stdout + templates.stderr)
        expect("the parameter text of both definitions",
               in_archive(paper, "check-listings.py", "probe.tex"), False,
               "0 failed", problems)

        # Every form of failure these checks catch, red.
        for case, text, checked_for, generated_for in SELF_TEST_RED:
            (paper / "probe.tex").write_text(text, encoding="utf-8")
            if generated_for is not None:
                expect(f"{case}, in gen-frames.py",
                       in_archive(paper, "gen-frames.py"), True, generated_for,
                       problems)
            expect(f"{case}, in check-listings.py",
                   in_archive(paper, "check-listings.py", "probe.tex"), True,
                   checked_for, problems)

        # A panel the generator has not seen has no frame.
        (paper / "probe.tex").write_text(SELF_TEST_PAIRED, encoding="utf-8")
        if in_archive(paper, "gen-frames.py").returncode != 0:
            problems.append("gen-frames.py failed before the unframed panel")
        (paper / "probe.tex").write_text(SELF_TEST_UNFRAMED, encoding="utf-8")
        expect("a panel with no generated frame",
               in_archive(paper, "check-listings.py", "probe.tex"), True,
               SELF_TEST_UNFRAMED_WANTED, problems)


def self_test() -> int:
    """Run these checks against a scratch paper that is wrong in one place.

    A case that does not report its own diagnostic, or that passes where it must
    fail, is recorded as a problem, and the run fails with it: a check whose red
    case has stopped failing is a check that has stopped guarding.

    The ways the self-test itself can fail to run are failures too -- a library
    that is not beside the paper, a script that is not beside this file, a
    scratch archive that cannot be written, a script run that cannot be launched
    -- each reported with its reason and a non-zero status rather than skipped
    quietly, so that no reader of either stream can take a run that checked
    nothing for one that passed.
    """
    here = Path(__file__).resolve().parent
    problems: list[str] = []
    absent = [str(here.parent / tree) for tree in SELF_TEST_TREES
              if not (here.parent / tree).is_dir()]
    if absent:
        problems.append(f"--self-test reads the library beside {here.name}: "
                        + ", ".join(absent) + " not found")
        return reported(problems)
    missing = [name for name in SELF_TEST_SCRIPTS if not (here / name).is_file()]
    if missing:
        problems.append("--self-test copies the scripts beside it: "
                        + ", ".join(missing) + " not found")
        return reported(problems)
    try:
        scratch_cases(here, problems)
    except OSError as error:
        problems.append(f"--self-test cannot use its scratch archive: {error}")
    return reported(problems)


def main(argv: list[str]) -> int:
    args = argv[1:]
    if "--self-test" in args:
        return self_test()
    here = Path(__file__).resolve().parent
    files = [Path(a) for a in args] or sorted(here.glob("*.tex"))
    if not files:
        print("no .tex files to check", file=sys.stderr)
        return 1
    problems: list[str] = []
    table = load_lookup(here, problems)
    fragments = laws = frames = 0
    for tex in files:
        if not tex.is_file():
            print(f"no such file: {tex}", file=sys.stderr)
            return 1
        calls, malformed = framescan.scan_frames(tex.read_text(encoding="utf-8"))
        for line, message in malformed:
            problems.append(f"{tex.name}:{line}: {message}")
        fragments += check_fragments(tex, calls, problems)
        laws += check_lawframes(tex, calls, problems)
        frames += check_frames(here, tex, table, calls, problems)
    stated = check_counts(here, problems)
    for problem in problems:
        print(problem)
    if not args:
        # The default run is the one a reader runs, so it carries the self-test
        # with it: the fixtures that keep these checks honest are then part of the
        # command rather than a second one a reader has to know to run.
        print()
        print("--- the checker's own self-test, on a scratch paper beside the library")
        if self_test():
            problems.append("the self-test did not check out")
            print(problems[-1])
    print(f"{fragments} quoted panels, {laws} law frames and {frames} generated "
          f"frames checked, {stated} generated counts checked, "
          f"{len(problems)} failed")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
