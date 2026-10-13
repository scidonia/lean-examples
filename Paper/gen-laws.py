#!/usr/bin/env python3
"""Generate Paper/laws.tex, the paper's law frames, and Paper/counts.tex, the
numbers its prose states about the library.

Each frame quotes the *statement* of a declaration, ending at the line where
the statement is complete (`:=`, or the last signature line for a clause-style
definition).  Nothing is transcribed: the frames are line ranges into the
library, and check-listings.py re-checks every one of them against the source.

counts.tex holds one \\newcommand per number the paper's prose states -- the
public theorems the library publishes, the law statements and panels the
appendix reproduces, the theorems vendored from Lean's own model -- so no
numeral is typed by hand, and check-listings.py recomputes the file and fails
when it is stale.

Usage:  python3 gen-laws.py            # writes laws.tex and counts.tex
        python3 gen-laws.py --dry-run  # prints a report only
"""

import re
import sys
from pathlib import Path

import framescan

ROOT = Path(__file__).resolve().parent.parent
PAPER = Path(__file__).resolve().parent
# The two papers in this directory.  Each states its own panel count, so the
# counts below are computed per source rather than over both at once.
COMPANION = "unobservable-effects.tex"
LOWERING = "lowering.tex"
KINDS = "inductive|structure|class|abbrev|def|theorem|lemma"
ATTR = r"(?:@\[[^\]]*\]\s*)?"
OPEN, CLOSE = "([{", ")]}"

# A public theorem as the library writes one: what the paper counts.
THEOREM = re.compile(rf"^{ATTR}(theorem|lemma)\s")

# The reference count's module marks where its vendored block ends; the header
# says the declarations up to there are Lean's own model of the count, and the
# rest are this repository's.  The prose states both counts, so they are read
# from that mark rather than typed.
REFCOUNT = "Scidonia/FracPerm/StateVar/RefCount.lean"
VENDORED_END = "The declarations up to here are vendored"

# The declarations the paper names or leans on, grouped as the appendix
# presents them.  (module, declaration name)
GROUPS = [
    ("The ledger and the arithmetic of shares", [
        ("Scidonia/FracPerm/Ledger.lean", "held_nil"),
        ("Scidonia/FracPerm/Ledger.lean", "held_cons"),
        ("Scidonia/FracPerm/Ledger.lean", "held_erase_of_mem")]),
    ("Detachment in the value language", [
        ("Scidonia/FracPerm/StateVar/Value.lean", "noRef_loc"),
        ("Scidonia/FracPerm/StateVar/Value.lean", "noRef_pair"),
        ("Scidonia/FracPerm/StateVar/Value.lean", "noRef_loc_of_ne"),
        ("Scidonia/FracPerm/StateVar/Value.lean", "not_noRef_loc_self")]),
    ("The generic model", [
        ("Scidonia/FracPerm/StateVar/Model.lean", "primitive_detached"),
        ("Scidonia/FracPerm/StateVar/Model.lean", "replay_trace"),
        ("Scidonia/FracPerm/StateVar/Model.lean", "eval_of_run"),
        ("Scidonia/FracPerm/StateVar/Model.lean", "complete_run_value"),
        ("Scidonia/FracPerm/StateVar/Model.lean", "wf_leafSum"),
        ("Scidonia/FracPerm/StateVar/Model.lean", "wf_sharesPositive"),
        ("Scidonia/FracPerm/StateVar/Model.lean", "reading_step_is_read_or_leave"),
        ("Scidonia/FracPerm/StateVar/Model.lean", "reading_step_store"),
        ("Scidonia/FracPerm/StateVar/Model.lean", "wait_step"),
        ("Scidonia/FracPerm/StateVar/Model.lean", "writer_authority_add"),
        ("Scidonia/FracPerm/StateVar/Model.lean", "pstep_wf"),
        ("Scidonia/FracPerm/StateVar/Model.lean", "safe_result")]),
    ("The single-root heap", [
        ("Scidonia/FracPerm/StateVar/Heap.lean", "read_at_detached"),
        ("Scidonia/FracPerm/StateVar/Heap.lean", "write_at_valid"),
        ("Scidonia/FracPerm/StateVar/Heap.lean", "write_at_frame"),
        ("Scidonia/FracPerm/StateVar/Heap.lean", "snapshot_after_write"),
        ("Scidonia/FracPerm/StateVar/Heap.lean", "pstep_write_corresponds"),
        ("Scidonia/FracPerm/StateVar/Heap.lean", "readAt_step_observe"),
        ("Scidonia/FracPerm/StateVar/Heap.lean", "cannot_add_reader")]),
    ("The array witness and the bridge", [
        ("Scidonia/FracPerm/StateVar/Array.lean", "arrayObserve_detached"),
        ("Scidonia/FracPerm/StateVar/Array.lean", "encodeArrayRead_injective"),
        ("Scidonia/FracPerm/StateVar/Array.lean", "arrayReplace_size"),
        ("Scidonia/FracPerm/StateVar/Array.lean", "arrayReplace_bounds"),
        ("Scidonia/FracPerm/StateVar/Array.lean", "bridge_val"),
        ("Scidonia/FracPerm/StateVar/Array.lean", "bridge_pval"),
        ("Scidonia/FracPerm/StateVar/Array.lean", "runFresh_eq_pval")]),
    ("The description universe and transport", [
        ("Scidonia/FracPerm/StateVar/Universe.lean", "encodeEl_injective"),
        ("Scidonia/FracPerm/StateVar/Universe.lean", "encodeEl_noRef"),
        ("Scidonia/FracPerm/StateVar/Universe.lean", "universe_read_after_replace"),
        ("Scidonia/FracPerm/StateVar/Universe.lean", "universe_read_detached"),
        ("Scidonia/FracPerm/StateVar/Universe.lean", "universe_write_at_valid"),
        ("Scidonia/FracPerm/StateVar/Universe.lean", "universe_write_at_frame"),
        ("Scidonia/FracPerm/StateVar/Universe.lean", "universe_snapshot_after_write"),
        ("Scidonia/FracPerm/StateVar/Universe.lean", "transport_read_after_replace")]),
    ("The slot", [
        ("Scidonia/FracPerm/StateVar/Slot.lean", "decode_encode"),
        ("Scidonia/FracPerm/StateVar/Slot.lean", "encode_decode"),
        ("Scidonia/FracPerm/StateVar/Slot.lean", "lifted_iff"),
        ("Scidonia/FracPerm/StateVar/Slot.lean", "slot_read_after_replace"),
        ("Scidonia/FracPerm/StateVar/Slot.lean", "slot_snapshot_full7_full9"),
        ("Scidonia/FracPerm/StateVar/Slot.lean", "slot_shape_change"),
        ("Scidonia/FracPerm/StateVar/Slot.lean", "slot_full_round_trip")]),
    ("Layouts, paths and the take-out", [
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "append_left"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "append_right"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "append_index"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "not_disjoint_here_left"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "disjoint_left_iff"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "disjoint_index_ne"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "encodeObs_injective"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "encodeObs_noRef"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "setLeaf_failed"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "read_detached"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "snapshot_after_setLeaf"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "read_frame"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "array_root_not_observable"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "describedLayout_read_after_replace"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "describedLayout_primitive_detached"),
        ("Scidonia/FracPerm/StateVar/Layout5.lean", "describedLayout_write_at_frame")]),
    ("The sealed class", [
        ("Scidonia/FracPerm/StateVar/Sealed.lean", "sealedLawful_Result"),
        ("Scidonia/FracPerm/StateVar/Sealed.lean", "sealedLawful_encodeRead"),
        ("Scidonia/FracPerm/StateVar/Sealed.lean", "toState_ofState"),
        ("Scidonia/FracPerm/StateVar/Sealed.lean", "ofState_toState"),
        ("Scidonia/FracPerm/StateVar/Sealed.lean", "sealedRead_detached"),
        ("Scidonia/FracPerm/StateVar/Sealed.lean", "sealedRead_after_setLeaf"),
        ("Scidonia/FracPerm/StateVar/Sealed.lean", "sealedSnapshot"),
        ("Scidonia/FracPerm/StateVar/Sealed.lean", "sealedRead_frame"),
        ("Scidonia/FracPerm/StateVar/Sealed.lean", "sealedSetLeaf_failed")]),
    ("The reference count", [
        ("Scidonia/FracPerm/StateVar/RefCount.lean", "not_exclusive_incRefN_one"),
        ("Scidonia/FracPerm/StateVar/RefCount.lean", "decRef_two"),
        ("Scidonia/FracPerm/StateVar/RefCount.lean", "not_exclusive_of_isMt"),
        ("Scidonia/FracPerm/StateVar/RefCount.lean", "markMtRc_not_exclusive"),
        ("Scidonia/FracPerm/StateVar/RefCount.lean", "not_exclusive_of_neverFreed"),
        ("Scidonia/FracPerm/StateVar/RefCount.lean", "run_never_exclusive"),
        ("Scidonia/FracPerm/StateVar/RefCount.lean", "takeOut_refCount_eq_one")]),
    ("The structured model", [
        ("Scidonia/FracPerm/Structured/Model.lean", "step_get"),
        ("Scidonia/FracPerm/Structured/Model.lean", "step_size"),
        ("Scidonia/FracPerm/Structured/Model.lean", "replay_trace"),
        ("Scidonia/FracPerm/Structured/Model.lean", "eval_of_run"),
        ("Scidonia/FracPerm/Structured/Model.lean", "complete_run_value"),
        ("Scidonia/FracPerm/Structured/Model.lean", "wf_leafSum"),
        ("Scidonia/FracPerm/Structured/Model.lean", "wf_sharesPositive"),
        ("Scidonia/FracPerm/Structured/Model.lean", "reading_step_is_read_or_leave"),
        ("Scidonia/FracPerm/Structured/Model.lean", "reading_step_store"),
        ("Scidonia/FracPerm/Structured/Model.lean", "wait_step"),
        ("Scidonia/FracPerm/Structured/Model.lean", "set_step"),
        ("Scidonia/FracPerm/Structured/Model.lean", "set_step_size"),
        ("Scidonia/FracPerm/Structured/Model.lean", "writer_authority_add")]),
    ("What the permission discipline refuses", [
        ("ScidoniaTest/FracPerm.lean", "n1_write_while_read_outstanding"),
        ("ScidoniaTest/FracPerm.lean", "n2_release_twice"),
        ("ScidoniaTest/FracPerm.lean", "n3_read_with_returned_token"),
        ("ScidoniaTest/FracPerm.lean", "n4_overcommit"),
        ("ScidoniaTest/FracPerm.lean", "n4b_reused_ghost_id"),
        ("ScidoniaTest/FracPerm.lean", "n5_unreturned_read"),
        ("ScidoniaTest/FracPerm.lean", "w3_escaped_token")]),
    ("Countermodels: the laws and the count are not vacuous", [
        ("ScidoniaTest/StateVar.lean", "bad_read_rejected"),
        ("ScidoniaTest/StateVar.lean", "bad_write_rejected"),
        ("ScidoniaTest/StateVar.lean", "bad_encode_rejected"),
        ("ScidoniaTest/Model5.lean", "leakyArray_read_returns_state"),
        ("ScidoniaTest/Model5.lean", "leaky_root_not_detached"),
        ("ScidoniaTest/Count.lean", "one_is_exclusive"),
        ("ScidoniaTest/Count.lean", "stuckSt_is_unshared_not_exclusive"),
        ("ScidoniaTest/Count.lean", "shared_count_is_not_exclusive"),
        ("ScidoniaTest/Count.lean", "not_exclusive_after_handOff"),
        ("ScidoniaTest/Count.lean", "takeOut_counts_at_one")]),
]


def statement_end(lines, i):
    """The first line at which the statement starting at line `i` is complete.

    A line carrying `:=` outside every bracket ends a statement.  A line
    opening a clause (`| pat => ...`) starts a proof, so the statement ended on
    the line before it.
    """
    depth = 0
    for k in range(i, min(len(lines), i + 30)):
        line = lines[k]
        if k > i and re.match(r"^\s*\|", line):
            return k - 1
        for j, c in enumerate(line):
            if c in OPEN:
                depth += 1
            elif c in CLOSE:
                depth -= 1
            elif c == ":" and depth == 0 and line[j + 1:j + 2] == "=":
                return k
    return min(len(lines) - 1, i + 30)


def locate(name, module):
    """The (first, last) line of the declaration `name` in `module`."""
    rx = re.compile(rf"^{ATTR}({KINDS})\s+{re.escape(name)}(?![\w'])")
    lines = (ROOT / module).read_text(encoding="utf-8").splitlines()
    for i, line in enumerate(lines):
        kind = rx.match(line)
        if not kind:
            continue
        start = i - 1 if i and re.match(r"^\s*@\[", lines[i - 1]) else i
        if kind.group(1) in ("inductive", "structure", "class"):
            j, last = i + 1, i
            while j < len(lines):
                if not lines[j].strip():
                    j += 1
                    continue
                if not lines[j][0].isspace() and not lines[j].startswith("deriving"):
                    break
                last, j = j, j + 1
            end = last
        else:
            end = statement_end(lines, i)
        return start + 1, end + 1
    return None


def published_theorems():
    """How many public theorems the library under Scidonia/ publishes."""
    total = 0
    for path in sorted(ROOT.glob("Scidonia/**/*.lean")):
        for line in path.read_text(encoding="utf-8").splitlines():
            if THEOREM.match(line):
                total += 1
    return total


def quoted_laws():
    """How many law frames the appendix reproduces."""
    return sum(len(items) for _, items in GROUPS)


def frames_from(module):
    """How many of the appendix's law frames come from `module`."""
    return sum(1 for _, items in GROUPS for path, _ in items if path == module)


def vendored_theorems():
    """How many of the reference count's theorems are Lean's own model.

    The public theorems above the module's mark for the end of its vendored
    block are the vendored ones; those below it are this repository's.
    """
    lines = (ROOT / REFCOUNT).read_text(encoding="utf-8").splitlines()
    for i, line in enumerate(lines):
        if VENDORED_END in line:
            return sum(1 for line in lines[:i] if THEOREM.match(line))
    raise SystemExit(f"{REFCOUNT}: no {VENDORED_END!r} line to split the "
                     f"vendored block at")


def panel_counts(tex_name):
    """(panels in the body, panels in the appendix) one paper's sources ask for.

    A panel is a `\\codeframe` call naming a range of the library, recognized by
    the rule the checker uses, so a line that carries two calls quotes two panels
    and is counted as two: the number the prose states is the panels, not the
    lines that happen to hold them.  The body's are the ones above `\\appendix`,
    and the appendix's are the ones below it. Each paper's count is its own: two
    papers quote the library here, and a count that mixed them would be a numeral
    neither paper could state.
    """
    text = (PAPER / tex_name).read_text(encoding="utf-8")
    lines = text.splitlines()
    end = next((i for i, line in enumerate(lines)
                if line.strip() == "\\appendix"), len(lines))
    calls, _ = framescan.scan_frames(text)
    per_line: dict[int, int] = {}
    for kind, line, *_ in calls:
        if kind == "codeframe":
            per_line[line] = per_line.get(line, 0) + 1
    return (sum(n for line, n in per_line.items() if line <= end + 1),
            sum(n for line, n in per_line.items() if line > end + 1))


def counts():
    """The numbers the papers' prose states, in the order the file writes them."""
    body, appendix = panel_counts(COMPANION)
    lowering, _ = panel_counts(LOWERING)
    return [
        ("theoremcount", "public theorems under Scidonia/", published_theorems()),
        ("vendoredtheoremcount", "of them vendored from Lean's own model",
         vendored_theorems()),
        ("lawcount", "law statements the appendix reproduces", quoted_laws()),
        ("panelcount", "panels the permission paper quotes", body + appendix),
        ("appendixpanelcount", "of them in the appendix", appendix),
        ("refcountframecount", "frames of the reference-count section",
         frames_from(REFCOUNT)),
        ("loweringpanelcount", "panels the lowering paper quotes", lowering),
    ]


def counts_text():
    """The contents of counts.tex: one \\newcommand per number the prose states."""
    header = (
        "% Generated from the library by gen-laws.py; do not edit by hand.\n"
        "% The numbers the paper's prose states about the library and about the\n"
        "% frames it quotes, one \\newcommand each, so no numeral is typed by hand.\n"
        "% The paper's preamble reads this file, and check-listings.py recomputes\n"
        "% it from the library and from the paper's own call sites.\n\n")
    return header + "".join(
        f"\\newcommand{{\\{name}}}{{{value}}}  % {what}\n"
        for name, what, value in counts())


def main(argv):
    frames, missing, report = [], [], []
    for title, items in GROUPS:
        frames.append(f"\\subsection{{{title}}}")
        for module, name in items:
            span = locate(name, module)
            if span is None:
                missing.append((module, name))
                continue
            lo, hi = span
            body = (ROOT / module).read_text(encoding="utf-8").splitlines()[lo - 1:hi]
            report.append(f"  {name:38s} {module.split('/')[-1]}:{lo}-{hi} ({hi-lo+1})")
            if hi - lo + 1 > 6:
                report[-1] += "   <-- long"
            frames.append(
                f"\\lawframe{{{module}}}{{{lo}-{hi}}}"
                f"{{{name.replace('_', chr(92) + '_')}}}")
        frames.append("")

    count = sum(len(items) for _, items in GROUPS)
    print(f"frames: {count - len(missing)} of {count}")
    if missing:
        print("MISSING:", missing)
    print(f"public theorems in Scidonia/**: {published_theorems()}")
    if "--verbose" in argv:
        print("\n".join(report))

    if "--dry-run" in argv:
        return 1 if missing else 0

    header = (
        "% Generated from the library by gen-laws.py; do not edit by hand.\n"
        "% Each \\lawframe{module}{lines}{name} quotes the statement of `name` from\n"
        "% that module.  check-listings.py verifies that every range still holds the\n"
        "% declaration it names, so the appendix cannot drift from the library.\n\n")
    (PAPER / "laws.tex").write_text(header + "\n".join(frames), encoding="utf-8")
    print("wrote Paper/laws.tex")
    (PAPER / "counts.tex").write_text(counts_text(), encoding="utf-8")
    print("wrote Paper/counts.tex")
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
