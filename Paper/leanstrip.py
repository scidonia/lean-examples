#!/usr/bin/env python3
"""Strip Lean comments, for the paper's frames and for the check on them.

The paper quotes a line range of a library file, and the frames show that range
with comments removed: a frame is code, not documentation.  Removing them is a
transformation, so both the generator (`gen-frames.py`) and the checker
(`check-listings.py`) go through this module: the checker recomputes what the
generator should have written, which is what makes the frames falsifiable
rather than merely plausible.

The rules are Lean's:

* `--` runs to the end of the line;
* `/- ... -/` is a block comment, and block comments nest;
* neither applies inside a string literal (or a character literal).

A quoted range can begin or end inside a block comment, so the depth entering
the range is computed from the lines above it: a range that starts in the middle
of a doc comment does not leak the tail of that comment into the frame.

A line that holds only a comment is dropped.  A line that was blank in the
source stays blank, so the author's paragraphing survives; a trailing comment is
cut from its line.
"""


def strip_line(line: str, depth: int) -> tuple[str, int, bool]:
    """Strip comments from one line.

    `depth` is the block-comment nesting carried in from the previous line.
    Returns the line's code, the depth carried out, and whether the source line
    was blank (which the caller keeps, unlike a comment-only line).
    """
    blank_source = not line.strip()
    code = []
    i, n = 0, len(line)
    while i < n:
        if depth:
            if line.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif line.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                i += 1
            continue
        if line.startswith("/-", i):
            depth, i = 1, i + 2
            continue
        if line.startswith("--", i):
            break
        c = line[i]
        if c == '"':
            j = i + 1
            while j < n:
                if line[j] == "\\" and j + 1 < n:
                    j += 2
                elif line[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            code.append(line[i:j])
            i = j
            continue
        if c == "'" and i + 2 < n and line[i + 2] == "'":
            code.append(line[i:i + 3])
            i += 3
            continue
        code.append(c)
        i += 1
    return "".join(code).rstrip(), depth, blank_source


def depth_before(lines: list[str], upto: int) -> int:
    """The block-comment nesting in effect just before line `upto` (1-based)."""
    depth = 0
    for line in lines[:upto - 1]:
        _, depth, _ = strip_line(line, depth)
    return depth


def strip_comments(text: str, depth: int = 0) -> str:
    """The lines of `text` that hold code, with trailing comments cut."""
    out = []
    for line in text.splitlines():
        code, depth, blank_source = strip_line(line, depth)
        if code:
            out.append(code)
        elif blank_source and out:
            out.append("")
    # One blank line where the author had a run of them, none at the edges.
    compact = []
    for line in out:
        if line or (compact and compact[-1]):
            compact.append(line)
    return "\n".join(compact).strip("\n")


def frame_body(all_lines: list[str], lo: int, hi: int) -> str:
    """The frame for lines `lo`--`hi` of a file (1-based, inclusive)."""
    quoted = "\n".join(all_lines[lo - 1:hi])
    return strip_comments(quoted, depth_before(all_lines, lo))
