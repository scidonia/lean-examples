#!/usr/bin/env python3
"""Check that every frame in the paper still quotes what it claims.

Four kinds of check, all against the library:

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
      recomputes it.

  counts.tex
      the generated counts must be exactly what gen-laws.py derives from the
      library and from the paper's own call sites, recomputed here.  This is
      what keeps a stated number -- the theorems the library publishes, the
      panels the paper quotes -- from outliving what it counts.

Usage:  python3 check-listings.py [file.tex ...]      # default: every *.tex here
Exit status 0 when every frame and count checks out, 1 otherwise.
"""

import importlib.util
import re
import sys
from pathlib import Path

import leanstrip

CHECK = re.compile(r"^\s*%\s*!check:\s*(?P<frag>.*\S)\s*$")
FRAME = re.compile(
    r"\\codeframe\[linerange=(?P<lo>\d+)-(?P<hi>\d+)\]\{(?P<path>[^}]*)\}"
)
LAWFRAME = re.compile(
    r"\\lawframe\{(?P<path>[^}]*)\}\{(?P<lo>\d+)-(?P<hi>\d+)\}\{(?P<name>[^}]*)\}"
)
LOOKUP = re.compile(
    r"\\expandafter\\def\\csname cf@(?P<path>.*)@(?P<lo>\d+)-(?P<hi>\d+)"
    r"\\endcsname\{(?P<key>[^}]*)\}"
)
# The bracket argument of a frame call, in any shape, so that a call the pattern
# above cannot resolve is seen rather than passed over.  An argument that is a call
# at all is a line range or one of the shape-and-colour macros' own parameters;
# `code_of` then drops what a comment holds, since that is not a call either.
SHAPE = re.compile(r"\\codeframe\[linerange=([^\]]*)\]")
RANGE = re.compile(r"\d+-\d+")
PARAM = re.compile(r"#\d+(?:-#\d+)?")
KINDS = "inductive|structure|class|abbrev|def|theorem|lemma"


def code_of(line: str) -> str:
    """`line` up to its LaTeX comment, if it has one.

    LaTeX ends the line at an unescaped per cent, so a `\\codeframe` after one is
    text the typesetter never reaches: it is not a call, and the `%!check:` beside
    it is not paired with it.  `\\%` is a literal per cent and does not begin a
    comment.
    """
    escaped = False
    for i, ch in enumerate(line):
        if ch == "%" and not escaped:
            return line[:i]
        escaped = ch == "\\" and not escaped
    return line


def normalise(text: str) -> str:
    """Collapse runs of whitespace so that indentation does not matter."""
    return re.sub(r"\s+", " ", text).strip()


def read_source(path: Path, limit: int, context: str):
    """The lines of `path`, or None after reporting that it cannot be read."""
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        print(f"{context}: cannot read {path}: {error}")
        return None
    if limit > len(lines):
        print(f"{context}: {path} has only {len(lines)} lines, range is ..{limit}")
        return None
    return lines


def check_fragments(tex: Path, problems: list[str]) -> int:
    """Verify each %!check: directive against the frame that follows it."""
    lines = tex.read_text(encoding="utf-8").splitlines()
    pending, checked = None, 0
    for number, line in enumerate(lines, start=1):
        match = CHECK.match(line)
        if match:
            pending = (number, match.group("frag"))
            continue
        match = FRAME.search(line)
        if not match:
            continue
        if pending is None:
            problems.append(f"{tex.name}:{number}: frame without a %!check:")
            continue
        directive, fragment = pending
        pending, checked = None, checked + 1
        where = f"{tex.name}:{directive}"
        lo, hi = int(match.group("lo")), int(match.group("hi"))
        body = read_source(tex.parent / match.group("path"), hi, where)
        if body is None:
            continue
        if normalise(fragment) not in normalise("\n".join(body[lo - 1:hi])):
            problems.append(
                f"{where}: {match.group('path')}:{lo}-{hi} does not contain\n"
                f"    {fragment}")
    if pending is not None:
        problems.append(f"{tex.name}:{pending[0]}: trailing %!check: with no frame")
    return checked


def check_calls(tex: Path, problems: list[str]) -> int:
    """Frame calls in a shape no frame can be generated for.

    A call is `\\codeframe[linerange=lo-hi]{path}`, with `lo == hi` for a single
    line. A definition such as a `\\lawframe`'s body writes
    `\\codeframe[linerange=#2]{../#1}`, whose argument is a macro parameter and not
    a range; nor is a call one written inside a comment, which the typesetter never
    reaches. Every other argument that is not `lo-hi` is a call with no frame, so
    the `%!check:` directive before it would be paired with whatever frame follows.
    It is reported rather than skipped.
    """
    found = 0
    for number, line in enumerate(tex.read_text(encoding="utf-8").splitlines(), 1):
        for match in SHAPE.finditer(code_of(line)):
            arg = match.group(1)
            if RANGE.fullmatch(arg) or PARAM.fullmatch(arg):
                continue
            problems.append(f"{tex.name}:{number}: not a "
                            f"\\codeframe[linerange=lo-hi]{{path}} call: "
                            f"{line.strip()}")
            found += 1
    return found


def check_lawframes(tex: Path, problems: list[str]) -> int:
    """Verify each law frame against the declaration it names."""
    text = tex.read_text(encoding="utf-8")
    checked = 0
    for match in LAWFRAME.finditer(text):
        number = text.count("\n", 0, match.start()) + 1
        where = f"{tex.name}:{number}"
        name = match.group("name").replace("\\_", "_").replace("\\%", "%")
        lo, hi = int(match.group("lo")), int(match.group("hi"))
        module = match.group("path")
        body = read_source(tex.parent / ".." / module, hi, where)
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


def check_frames(here: Path, tex: Path, table: dict, problems: list[str]) -> int:
    """Verify every generated frame against the range it was generated from."""
    text = tex.read_text(encoding="utf-8")
    wanted = [(m.group("path"), int(m.group("lo")), int(m.group("hi")), m.start())
              for m in FRAME.finditer(text)]
    wanted += [("../" + m.group("path"), int(m.group("lo")), int(m.group("hi")), m.start())
               for m in LAWFRAME.finditer(text)]
    checked = 0
    for path, lo, hi, at in wanted:
        where = f"{tex.name}:{text.count(chr(10), 0, at) + 1}"
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
        lines = read_source(source, hi, where)
        if lines is None:
            continue
        want = leanstrip.frame_body(lines, lo, hi)
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


def main(argv: list[str]) -> int:
    here = Path(__file__).resolve().parent
    files = [Path(a) for a in argv[1:]] or sorted(here.glob("*.tex"))
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
        check_calls(tex, problems)
        fragments += check_fragments(tex, problems)
        laws += check_lawframes(tex, problems)
        frames += check_frames(here, tex, table, problems)
    stated = check_counts(here, problems)
    for problem in problems:
        print(problem)
    print(f"{fragments} quoted panels, {laws} law frames and {frames} generated "
          f"frames checked, {stated} generated counts checked, "
          f"{len(problems)} failed")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
