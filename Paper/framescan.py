#!/usr/bin/env python3
"""Recognize the paper's frame commands, so that none can pass unrecognized.

A frame is asked for by one of two LaTeX commands:

    \\codeframe[linerange=lo-hi]{../path/to/Module.lean}
    \\lawframe{path/to/Module.lean}{lo-hi}{name}

The generator (`gen-frames.py`), the checker (`check-listings.py`) and the counts
(`gen-laws.py`) all need to know which calls the paper makes, and all three go
through this module so that they cannot disagree.  Before it, the generator and
the checker each matched the commands with their own patterns, and a form one
took for a call and the other did not could be left out of both the frames and
the checks on them.

Recognition is total.  It begins at every `\\codeframe` and `\\lawframe` in the
source the typesetter reaches -- comments blanked, since a command after an
unescaped per cent is text LaTeX never reads -- and then requires the whole
call: a numeric `lo-hi` range and a brace-delimited path, or three brace-
delimited arguments whose second is a numeric `lo-hi` range.  A missing bracket,
path or brace, a non-numeric or incomplete range, and a placeholder outside a
definition are therefore findings rather than forms no pattern happens to match.

Three occurrences are not calls: the range in the `\\codeframe` definition's
signature, the forwarded range in the `\\lawframe` definition's body, and the
`\\lawframe` that names its own definition.  Each is recognized by its definition
context, so a placeholder-shaped argument anywhere else is reported.
"""

import re

# Recognition begins at either command token and then requires the whole call.
COMMAND = re.compile(r"\\(?:codeframe|lawframe)")
# A call, matched strictly from the command token.  The bracket argument holds
# no bracket, brace or newline, so a call whose `]` or `{` is missing fails to
# match rather than running on to a later one.
CODEFRAME = re.compile(
    r"(?P<head>\\codeframe\[linerange=(?P<arg>[^\]{}\n]*)\])(?P<path>\{[^}\n]*\})?"
)
LAWFRAME = re.compile(
    r"\\lawframe\{(?P<path>[^}\n]*)\}\{(?P<arg>[^}\n]*)\}\{(?P<name>[^}\n]*)\}"
)
RANGE = re.compile(r"\d+-\d+")
# The definitions whose parameter text is syntax and not a call.
CODEFRAME_DEF = re.compile(r"\\def\\codeframe\[linerange=#1-#2\]#3\s*\{")
LAWFRAME_DEF = re.compile(r"\\newcommand\s*\{\s*\\lawframe\s*\}\s*\[3\]\s*\{")
LAWFRAME_BODY_CALL = re.compile(r"\\codeframe\[linerange=#2\]\{\.\./#1\}")


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


def source_without_comments(text: str) -> str:
    """Blank comments while preserving source offsets for the macro contexts."""
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
    """The spans of the parameter text that is syntax in the two definitions.

    A span is into the same offsets as `text`, so `scan_frames` can tell a
    definition's parameter text from a call by where it stands.
    """
    source = source_without_comments(text)
    templates: set[tuple[int, int]] = set()
    for definition in CODEFRAME_DEF.finditer(source):
        call = CODEFRAME.match(source, definition.start() + len("\\def"))
        if call:
            templates.add(call.span("head"))
    for definition in LAWFRAME_DEF.finditer(source):
        name = source.find("\\lawframe", definition.start(), definition.end())
        if name != -1:
            templates.add((name, name + len("\\lawframe")))
        opening = definition.end() - 1
        end = macro_body_end(source, opening)
        if end is None:
            continue
        for call in LAWFRAME_BODY_CALL.finditer(source, opening + 1, end - 1):
            head = CODEFRAME.match(source, call.start())
            if head:
                templates.add(head.span("head"))
    return templates


def codeframe_at(source: str, start: int, templates: set[tuple[int, int]]):
    """The call at a `\\codeframe` token, a template, or what is malformed.

    Returns `(call, problem)`: `call` is `(path, lo, hi, None)`, `problem` names
    what is wrong with the command.  Both None means the token is parameter text
    in a definition, and so neither a call nor a finding.
    """
    match = CODEFRAME.match(source, start)
    if match is None:
        return None, "malformed \\codeframe call: no [linerange=lo-hi]{path}"
    if match.span("head") in templates:
        return None, None
    arg, path = match.group("arg"), match.group("path")
    if path is None:
        return None, (f"malformed \\codeframe call: no {{path}} after "
                      f"[linerange={arg}]")
    if not RANGE.fullmatch(arg):
        return None, f"\\codeframe[linerange={arg}] is not a numeric lo-hi range"
    lo, hi = (int(part) for part in arg.split("-"))
    return (path[1:-1], lo, hi, None), None


def lawframe_at(source: str, start: int, templates: set[tuple[int, int]]):
    """The call at a `\\lawframe` token, the definition's name, or a finding.

    Returns the same pair as `codeframe_at`; `call` is
    `(path, lo, hi, name)`.
    """
    end = start + len("\\lawframe")
    if (start, end) in templates:
        return None, None
    match = LAWFRAME.match(source, start)
    if match is None:
        return None, "malformed \\lawframe call: no {path}{lo-hi}{name}"
    arg = match.group("arg")
    if not RANGE.fullmatch(arg):
        return None, (f"malformed \\lawframe call: {match.group('path')} range "
                      f"{arg!r} is not a numeric lo-hi range")
    lo, hi = (int(part) for part in arg.split("-"))
    return (match.group("path"), lo, hi, match.group("name")), None


def scan_frames(text: str):
    """Every frame command in `text`: the calls it asks for, and the malformed.

    Returns `(calls, malformed)`.  A call is `(kind, line, path, lo, hi, name)`,
    where `kind` is `"codeframe"` or `"lawframe"` and `name` is None for a
    codeframe.  A malformed entry is `(line, message)`, the message naming the
    command, what is wrong with it, and the line it stands on.  `line` is
    1-based in `text`.
    """
    source = source_without_comments(text)
    templates = macro_template_spans(text)
    lines = text.splitlines()
    calls, malformed = [], []
    for command in COMMAND.finditer(source):
        start = command.start()
        if command.group(0) == "\\codeframe":
            call, problem = codeframe_at(source, start, templates)
        else:
            call, problem = lawframe_at(source, start, templates)
        line = text.count("\n", 0, start) + 1
        if call is not None:
            calls.append((command.group(0)[1:], line) + call)
        elif problem is not None:
            malformed.append((line, f"{problem}: {lines[line - 1].strip()}"))
    return calls, malformed
