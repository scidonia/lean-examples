#!/usr/bin/env python3
"""Generate the paper's frames from the library.

A frame is a quoted line range of a library file, shown with its comments
removed (`leanstrip.py`).  The paper writes each frame as

    \\codeframe[linerange=lo-hi]{../path/to/Module.lean}

and this script turns every such call, in every .tex beside it, into a file
`frames/<key>.lean` holding the comment-free code, plus a lookup table
`frames/lookup.tex` that maps the call's (path, range) to that file.  The
paper's preamble reads the table, so a call site does not name its frame: it
names the source, and the frame follows from it.

`check-listings.py` recomputes `frames/<key>.lean` from the source and fails
when the two differ, so a frame cannot drift from the library it quotes, and a
frame's content is verified rather than asserted.

Usage:  python3 gen-frames.py [--dry-run]

A call whose source is missing or unreadable, a range its file does not reach,
a frame that comes out empty and a nonnumeric frame argument are each reported
and make the run fail, so a frame the paper asks for is never silently absent.
"""

import hashlib
import re
import sys
from pathlib import Path

import leanstrip

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CALL = re.compile(
    r"\\codeframe\[linerange=(?P<lo>\d+)-(?P<hi>\d+)\]\{(?P<path>[^}]*)\}"
)
# A law frame writes \lawframe{module}{lo-hi}{name}, and the macro turns that
# into \codeframe[linerange=lo-hi]{../module}, so the lookup key is the same
# shape as a panel's.
LAW = re.compile(
    r"\\lawframe\{(?P<path>[^}]*)\}\{(?P<lo>\d+)-(?P<hi>\d+)\}\{(?P<name>[^}]*)\}"
)
# A non-numeric argument is exempt only at the two actual macro templates: the
# range in \codeframe's definition signature and the forwarded range in
# \lawframe's definition body.  These are recognized by their definition context,
# not by accepting placeholder-shaped arguments in general.
SHAPE = re.compile(r"\\codeframe\[linerange=([^\]]*)\]")
RANGE = re.compile(r"\d+-\d+")
CODEFRAME_DEF = re.compile(r"\\def\\codeframe\[linerange=#1-#2\]#3\s*\{")
LAWFRAME_DEF = re.compile(
    r"\\newcommand\s*\{\s*\\lawframe\s*\}\s*\[3\]\s*\{"
)
LAWFRAME_BODY_CALL = re.compile(r"\\codeframe\[linerange=#2\]\{\.\./#1\}")


def code_of(line: str) -> str:
    """`line` up to its LaTeX comment, if it has one.

    LaTeX ends the line at an unescaped per cent, so a `\\codeframe` after one is
    text the typesetter never reaches: it is not a call, and can neither ask for a
    frame nor leave the `%!check:` beside it unpaired.  `\\%` is a literal per cent
    and does not begin a comment.
    """
    escaped = False
    for i, ch in enumerate(line):
        if ch == "%" and not escaped:
            return line[:i]
        escaped = ch == "\\" and not escaped
    return line


def source_without_comments(text: str) -> str:
    """Blank comments while preserving source offsets for macro-context checks."""
    result = []
    for line in text.splitlines(keepends=True):
        body = line.rstrip("\r\n")
        ending = line[len(body):]
        visible = code_of(body)
        result.append(visible + " " * (len(body) - len(visible)) + ending)
    return "".join(result)


def macro_body_end(source: str, opening: int) -> int | None:
    """The position after a macro body's matching closing brace, or None."""
    depth, escaped = 0, False
    for position in range(opening, len(source)):
        char = source[position]
        if char == "\\":
            escaped = not escaped
            continue
        if not escaped:
            if char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
                if depth == 0:
                    return position + 1
        escaped = False
    return None


def macro_template_spans(text: str) -> set[tuple[int, int]]:
    """The range arguments that are syntax in the two macro definitions."""
    source = source_without_comments(text)
    templates: set[tuple[int, int]] = set()
    for definition in CODEFRAME_DEF.finditer(source):
        shape = SHAPE.search(source, definition.start(), definition.end())
        if shape:
            templates.add(shape.span())
    for definition in LAWFRAME_DEF.finditer(source):
        opening = definition.end() - 1
        end = macro_body_end(source, opening)
        if end is None:
            continue
        for call in LAWFRAME_BODY_CALL.finditer(source, opening + 1, end - 1):
            shape = SHAPE.search(source, call.start(), call.end())
            if shape:
                templates.add(shape.span())
    return templates


def calls():
    """Every frame the paper asks for, and every nonnumeric call to reject.

    A call has a numeric `lo-hi` range. The only placeholder ranges that are not
    calls are the `\\codeframe` definition's parameter text and the forwarded
    range call inside the `\\lawframe` definition. Their exact source locations
    are recognized by `macro_template_spans`; a placeholder in any real call is
    reported, as is any other nonnumeric argument. Text after a LaTeX comment is
    not part of the source the typesetter reaches.
    """
    found, malformed = [], []
    for tex in sorted(HERE.glob("*.tex")):
        text = tex.read_text(encoding="utf-8")
        templates = macro_template_spans(text)
        offset = 0
        for number, raw_line in enumerate(text.splitlines(keepends=True), 1):
            line = raw_line.rstrip("\r\n")
            for match in SHAPE.finditer(code_of(line)):
                arg = match.group(1)
                span = (offset + match.start(), offset + match.end())
                if not RANGE.fullmatch(arg) and span not in templates:
                    malformed.append(f"{tex.name}:{number}: {line.strip()}")
            offset += len(raw_line)
        for match in CALL.finditer(text):
            key = (match.group("path"), int(match.group("lo")), int(match.group("hi")))
            if key not in found:
                found.append(key)
        for match in LAW.finditer(text):
            key = ("../" + match.group("path"),
                   int(match.group("lo")), int(match.group("hi")))
            if key not in found:
                found.append(key)
    return found, malformed


def key_of(path: str, lo: int, hi: int) -> str:
    return hashlib.sha1(f"{path}:{lo}-{hi}".encode()).hexdigest()[:12]


def main(argv):
    dry = "--dry-run" in argv
    out = HERE / "frames"
    out.mkdir(exist_ok=True)

    wanted, malformed = calls()
    table, report, empty = [], [], []
    failed = bool(malformed)
    for where in malformed:
        report.append(f"MALFORMED FRAME CALL {where}")
    for path, lo, hi in wanted:
        module = (HERE / path).resolve()
        if not module.is_file():
            report.append(f"MISSING SOURCE {path}")
            failed = True
            continue
        try:
            text = module.read_text(encoding="utf-8")
        except OSError as error:
            report.append(f"UNREADABLE SOURCE {path}: {error}")
            failed = True
            continue
        lines = text.splitlines()
        if hi > len(lines):
            report.append(f"RANGE PAST END {path}:{lo}-{hi} ({len(lines)} lines)")
            failed = True
            continue
        body = leanstrip.frame_body(lines, lo, hi)
        if not body.strip():
            empty.append(f"{path}:{lo}-{hi}")
            failed = True
        key = key_of(path, lo, hi)
        if not dry:
            (out / f"{key}.lean").write_text(body + "\n", encoding="utf-8")
        table.append((path, lo, hi, key))
        report.append(f"  {path}:{lo}-{hi} -> frames/{key}.lean "
                      f"({len(body.splitlines())} lines)")

    if not dry:
        header = (
            "% Generated by gen-frames.py; do not edit by hand.\n"
            "% Maps a \\codeframe call's (path, range) to its generated frame, so a\n"
            "% call site names the source and not the frame. The frames themselves are\n"
            "% frames/<key>.lean, comment-free copies of the ranges, checked by\n"
            "% check-listings.py against the library.\n\n"
        )
        table_tex = "\n".join(
            f"\\expandafter\\def\\csname cf@{path}@{lo}-{hi}\\endcsname{{{key}}}"
            for path, lo, hi, key in table)
        (out / "lookup.tex").write_text(header + table_tex + "\n", encoding="utf-8")
        # The directory is this script's output, so it holds the frames the papers
        # ask for and nothing else: a frame no call names is a leftover from a range
        # that has since moved, and leaving it would let an unread quote sit in the
        # tree.  A moved range is therefore a deletion and an addition, not a second
        # copy beside the first.
        wanted = {f"{key}.lean" for _, _, _, key in table} | {"lookup.tex"}
        for stale in sorted(out.glob("*.lean")):
            if stale.name not in wanted:
                stale.unlink()
                report.append(f"  removed frames/{stale.name} (no call names it)")

    print(f"{len(table)} frames from {len({p for p, _, _, _ in table})} modules")
    for line in report:
        print(line)
    if empty:
        print("EMPTY FRAMES:", empty)
    if dry:
        print("(dry run: nothing written)")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
