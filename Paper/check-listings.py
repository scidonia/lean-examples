#!/usr/bin/env python3
"""Check that every quoted frame in the paper still quotes what it claims.

Two kinds of frame, both read from the library by line range:

  %!check: <fragment>
  \\lstinputlisting[linerange=<lo>-<hi>]{<file>}
      the range must contain <fragment>;

  \\lawframe{<file>}{<lo>-<hi>}{<name>}
      the range must contain the declaration of <name> -- a line at which
      `theorem`/`def`/... followed by that name begins.

A line range drifts silently when the file above it changes, so every frame is
checked against the named source.  This checks the paper's quotations, not that
the Lean compiles: the library is built separately.

Usage:  python3 check-listings.py [file.tex ...]      # default: every *.tex here
Exit status 0 when every frame checks out, 1 otherwise.
"""

import re
import sys
from pathlib import Path

CHECK = re.compile(r"^\s*%\s*!check:\s*(?P<frag>.*\S)\s*$")
LISTING = re.compile(
    r"\\codeframe\[linerange=(?P<lo>\d+)-(?P<hi>\d+)\]\{(?P<path>[^}]*)\}"
)
LAWFRAME = re.compile(
    r"\\lawframe\{(?P<path>[^}]*)\}\{(?P<lo>\d+)-(?P<hi>\d+)\}\{(?P<name>[^}]*)\}"
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
    """Verify each %!check: directive against the listing that follows it."""
    lines = tex.read_text(encoding="utf-8").splitlines()
    pending, checked = None, 0
    for number, line in enumerate(lines, start=1):
        match = CHECK.match(line)
        if match:
            pending = (number, match.group("frag"))
            continue
        match = LISTING.search(line)
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
        problems.append(f"{tex.name}:{pending[0]}: trailing %!check: with no listing")
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


def main(argv: list[str]) -> int:
    here = Path(__file__).resolve().parent
    files = [Path(a) for a in argv[1:]] or sorted(here.glob("*.tex"))
    if not files:
        print("no .tex files to check", file=sys.stderr)
        return 1
    problems: list[str] = []
    fragments = laws = 0
    for tex in files:
        if not tex.is_file():
            print(f"no such file: {tex}", file=sys.stderr)
            return 1
        fragments += check_fragments(tex, problems)
        laws += check_lawframes(tex, problems)
    for problem in problems:
        print(problem)
    print(f"{fragments} quoted panels and {laws} law frames checked, "
          f"{len(problems)} failed")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
