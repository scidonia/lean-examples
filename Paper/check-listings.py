#!/usr/bin/env python3
"""Check that every frame in the paper still quotes what it claims.

Three kinds of check, all against the library:

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

Usage:  python3 check-listings.py [file.tex ...]      # default: every *.tex here
Exit status 0 when every frame checks out, 1 otherwise.
"""

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
KINDS = "inductive|structure|class|abbrev|def|theorem|lemma"


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
        fragments += check_fragments(tex, problems)
        laws += check_lawframes(tex, problems)
        frames += check_frames(here, tex, table, problems)
    for problem in problems:
        print(problem)
    print(f"{fragments} quoted panels, {laws} law frames and {frames} generated "
          f"frames checked, {len(problems)} failed")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
