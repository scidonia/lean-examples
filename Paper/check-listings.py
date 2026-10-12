#!/usr/bin/env python3
"""Check that each quoted listing still contains what the paper says it does.

The paper reads its code panels out of the library with
``\\lstinputlisting[linerange=...]{file}``.  A line range drifts silently when the
file above it changes, so every panel is preceded by a

    %!check: <fragment>

directive naming a fragment of the declaration the panel is claimed to quote.
This script pairs each directive with the ``\\lstinputlisting`` that follows it,
reads that file's named lines, and fails if the fragment is not among them.

Usage:  python3 check-listings.py [paper.tex]

Exit status is 0 when every panel checks out, 1 otherwise.
"""

import re
import sys
from pathlib import Path

CHECK = re.compile(r"^\s*%\s*!check:\s*(?P<frag>.*\S)\s*$")
LISTING = re.compile(
    r"\\lstinputlisting\[(?P<opts>[^\]]*)\]\{(?P<path>[^}]*)\}"
)
RANGE = re.compile(r"linerange\s*=\s*(?P<lo>\d+)\s*-\s*(?P<hi>\d+)")


def normalise(text: str) -> str:
    """Collapse runs of whitespace so that indentation does not matter."""
    return re.sub(r"\s+", " ", text).strip()


def main(argv: list[str]) -> int:
    tex = Path(argv[1] if len(argv) > 1 else "unobservable-effects.tex")
    if not tex.is_file():
        print(f"no such file: {tex}", file=sys.stderr)
        return 1

    lines = tex.read_text(encoding="utf-8").splitlines()
    pending: tuple[int, str] | None = None
    panels = 0
    failures = 0

    for number, line in enumerate(lines, start=1):
        match = CHECK.match(line)
        if match:
            pending = (number, match.group("frag"))
            continue

        match = LISTING.search(line)
        if not match:
            continue
        if pending is None:
            print(f"{tex}:{number}: listing without a %!check: directive")
            failures += 1
            continue

        directive_line, fragment = pending
        pending = None
        panels += 1

        source = tex.parent / match.group("path")
        span = RANGE.search(match.group("opts"))
        if span is None:
            print(f"{tex}:{number}: listing without a linerange")
            failures += 1
            continue
        lo, hi = int(span.group("lo")), int(span.group("hi"))

        try:
            body = source.read_text(encoding="utf-8").splitlines()
        except OSError as error:
            print(f"{tex}:{directive_line}: cannot read {source}: {error}")
            failures += 1
            continue

        if hi > len(body):
            print(f"{tex}:{directive_line}: {source} has only {len(body)} lines, "
                  f"range is {lo}-{hi}")
            failures += 1
            continue

        quoted = normalise("\n".join(body[lo - 1:hi]))
        if normalise(fragment) not in quoted:
            print(f"{tex}:{directive_line}: {source}:{lo}-{hi} does not contain")
            print(f"    {fragment}")
            failures += 1

    if pending is not None:
        print(f"{tex}:{pending[0]}: trailing %!check: directive with no listing")
        failures += 1

    print(f"{panels} panels checked, {failures} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
