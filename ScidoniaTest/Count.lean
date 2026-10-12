/-
Compile-time checks for `Scidonia.FracPerm.StateVar.RefCount`.

The module is the counter-level vocabulary the write path reads: the two tests a
write may make of a count, and the facts at the count level that its discipline
rests on. It has no pre-fix behaviour to observe — it is a proof module — so the
checks here are the counts the predicates distinguish and the arithmetic the
adjustments do, met from outside the module. They are of four kinds:

* **The two tests**, on counts that tell them apart: the exclusive count itself,
  the count a single-threaded overflow freezes at (`isUnshared` and not
  `IsExclusive`), a persistent count, and the thread-shared count a
  `Task.spawn` measurement leaves.
* **The hazard pair** `1 → 2 → 1`: one extra reference takes the exclusive count
  to 2 and costs the in-place write, and the release takes it back to 1. The
  drop's step is a theorem; the increment's step is a `#guard`, because the
  kernel cannot reduce the `USize` comparison `incRefN`'s guard makes — the same
  limit the vendored file's own concrete examples hit, where they are proved by
  native evaluation instead.
* **The take-out** at the counts a one-reference cell hands out, so the
  arithmetic of `takeOut_refCount_eq_one` is exercised and not merely stated.
* **The axioms**, in the three groups their provenance puts them in: the
  vendored theorems, printed and read (some of their proofs use `bv_decide`,
  which decides by native evaluation and asserts the result as an axiom, and
  whether a given one carries a certificate is read from its own printed list —
  thirteen of the seventeen do; they are not this repository's to remove); this
  repository's facts derived from a vendored theorem, printed, whose docstring
  names the declaration they inherit their axioms from; and this repository's own
  facts, whose lists the check *asserts* to be the standard kernel principles and
  nothing else, so an axiom appearing in one fails the build rather than being
  read past.
-/
import Scidonia.FracPerm.StateVar.RefCount

open Scidonia.FracPerm.StateVar.RefCount

namespace ScidoniaTest.Count

/-! ## The two tests, on counts that tell them apart -/

/-- An exclusive count is inhabited: one reference, single-threaded. This is the
affirmative control for the hypothesis of `not_exclusive_incRefN_one` — without
it, that statement would say nothing about any count. -/
theorem one_is_exclusive : IsExclusive (1 : Int32) := by
  simp only [IsExclusive, isSt, decide_eq_true_eq]
  grind

/-- The count a single-threaded increment freezes at once it overflows reads as
unshared and not as exclusive: it stands for more references than it can track,
so `IsUnshared` is strictly weaker than `IsExclusive`, and the two are not
interchangeable at a write. This is the stuck single-threaded case.

It is stated through the vendored `LEAN_RC_STUCK_ST_eq`, so it inherits that
theorem's axioms — the standard kernel principles and no certificate, as the
Axioms section below prints. -/
theorem stuckSt_is_unshared_not_exclusive :
    IsUnshared LEAN_RC_STUCK_ST ∧ ¬ IsExclusive LEAN_RC_STUCK_ST := by
  constructor
  · simp only [IsUnshared, isUnshared, LEAN_RC_STUCK_ST_eq]
    grind
  · simp only [IsExclusive, isSt, LEAN_RC_STUCK_ST_eq, decide_eq_true_eq, not_and]
    grind

/-- A persistent count is never freed by a drop and is not exclusive. -/
theorem persistent_is_neverFreed_not_exclusive :
    isNeverFreed (0 : Int32) = true ∧ ¬ IsExclusive (0 : Int32) :=
  ⟨by decide, not_exclusive_of_neverFreed 0 (by decide)⟩

/-- The `Task.spawn` measurement: sharing the exclusive count leaves the
thread-shared count `-1`, which is not exclusive, so a write meeting it cannot
store in place. -/
theorem shared_count_is_not_exclusive :
    isMt (markMtRc (1 : Int32)) ∧ ¬ IsExclusive (markMtRc (1 : Int32)) :=
  ⟨by decide, markMtRc_not_exclusive 1⟩

/-! ## The hazard pair `1 → 2 → 1`

One extra reference takes the exclusive count to 2 and costs the in-place write;
dropping it returns the count to 1. The drop's step is a theorem. The
increment's step is a `#guard` on an evaluated result: `decide` cannot reduce
`incRefN`, whose guard is a `USize` comparison and whose platform word size is
opaque to the kernel, so the check is made by evaluation rather than by proof.
-/

/-
The hand-off's step: the exclusive count with one extra reference. Checked by
evaluation — see the section note. A doc comment cannot stand here: Lean's
parser rejects a `#guard` directly after one, so these carry plain comments.
-/
#guard decide (incRefN (1 : Int32) 1 = 2)

/-
The count the hand-off freezes at for a huge increment is the count
`stuckSt_is_unshared_not_exclusive` is stated at: the stuck case is reachable
from the model, not an unreachable constant.
-/
#guard decide (incRefN (1 : Int32) 0x7fffffff = LEAN_RC_STUCK_ST)

/-- The release's step: dropping the second reference returns the exclusive
count. A theorem, so this half of the pair is proved rather than evaluated. -/
theorem decRef_two_is_one : decRef (2 : Int32) = some 1 := by decide

/-
The pair composed: the increment's count, dropped, is the exclusive count
again. Checked by evaluation, for the reason above.
-/
#guard decide (decRef (incRefN (1 : Int32) 1) = some 1)

/-
The affirmative control for the three `#guard`s above: a false equation is
reported, so a guard is a detector that fires and not a command that passes
whatever it is given. The message is pinned as the toolchain prints it.
-/
/--
error: Expression
  decide (incRefN 1 1 = 3)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (incRefN (1 : Int32) 1 = 3)

/-- The cost of the hand-off, at the concrete count: after the increment the
count is no longer exclusive, so the write that stores in place is not
available. -/
theorem not_exclusive_after_handOff : ¬ IsExclusive (incRefN (1 : Int32) 1) :=
  not_exclusive_incRefN_one 1 one_is_exclusive

/-! ## The take-out at the counts a one-reference cell hands out -/

/-- The cell's count is 1, the handed-over count is 2, and the count left after
the release is 1: the three hypotheses of `takeOut_refCount_eq_one` at the
counts they describe, and its conclusion discharged through it. -/
theorem takeOut_counts_at_one :
    refCount (1 : Int32) = 1 ∧ refCount (2 : Int32) = 2 ∧
      refCount (1 : Int32) = 1 :=
  ⟨by decide, by decide,
   takeOut_refCount_eq_one 1 2 1 (by decide) (by decide) (by decide)⟩

/-! ## The counts themselves, printed

The two tests and the two adjustments at the counts the controls are about. -/

#eval (isUnshared LEAN_RC_STUCK_ST, isSt LEAN_RC_STUCK_ST, isUnshared (0 : Int32),
       isSt (0 : Int32), isMt (markMtRc (1 : Int32)), incRefN (1 : Int32) 1,
       decRef (2 : Int32))

/-! ## Axioms of representative theorems

Three groups, each read the way its provenance demands. The standard kernel
principles are `propext`, `Classical.choice` and `Quot.sound`; any other name in
a list is an axiom the proof rests on.

### The vendored theorems: printed and read

The block below is the Lean FRO's, so its lists are printed rather than asserted:
they are not this repository's to change. All seventeen of its public theorems are
printed. Thirteen carry at least one generated certificate axiom beside
`propext`, `Classical.choice` and `Quot.sound`; the axiom is named after the
declaration whose proof introduced it, which for several of them is a dependency
rather than the theorem itself — `run_spec`'s forty come entirely from other
declarations, and `incRefN_spec_nat`'s thirty likewise. Four print none —
`LEAN_RC_STUCK_ST_eq`, `incRefHugeMt_id`, `decRef_spec` and
`frozen_shared_count_stays_shared` — and of those only `LEAN_RC_STUCK_ST_eq`
invokes `bv_decide` at all: `incRefHugeMt_id` is `mvcgen` then `grind`,
`decRef_spec` is `grind`'s, and `frozen_shared_count_stays_shared` is `omega`'s.
`isSt` and `refCount` are printed with them: `isSt`
rests on nothing, and `refCount` on `propext` alone. -/

#print axioms isSt
#print axioms refCount
#print axioms LEAN_RC_STUCK_ST_eq
#print axioms isUnstuckMt_unsigned
#print axioms incRefHugeMt_id
#print axioms incRefHugeMt_spec
#print axioms incRefN_spec
#print axioms decRef_spec
#print axioms isNeverFreed_unsigned
#print axioms incRefN_descends
#print axioms never_freed_is_absorbing
#print axioms markMtRc_spec
#print axioms markMtRc_shared
#print axioms decRef_stays_shared
#print axioms frozen_shared_count_stays_shared
#print axioms incRefN_ascends
#print axioms incRefN_spec_nat
#print axioms run_spec
#print axioms run_never_frees

/-! ### Facts derived from a vendored theorem: printed, their sources named

`run_never_exclusive` composes the vendored `run_never_frees` with this
repository's `not_exclusive_of_neverFreed`, so it inherits the axioms of
`run_never_frees` and adds none of its own — its docstring names that source, and
the list below is the vendored theorem's, certificate names and all.
`stuckSt_is_unshared_not_exclusive` is stated through the vendored
`LEAN_RC_STUCK_ST_eq`, which carries no certificate, so it inherits the standard
principles only. -/

#print axioms run_never_exclusive
#print axioms stuckSt_is_unshared_not_exclusive

/-! ### This repository's own facts: asserted

`not_exclusive_incRefN_one`, `decRef_two`, `not_exclusive_of_isMt`,
`markMtRc_not_exclusive`, `not_exclusive_of_neverFreed` and
`takeOut_refCount_eq_one` are proved with `grind`, `simp` and `decide`, which are
kernel-checked and add no axiom, so each must rest on the standard kernel
principles and no others. These are asserted rather than printed: each
`#guard_msgs` pins the message `#print axioms` emits, so a proof that acquires
any other axiom fails the build instead of printing a longer list for a reader to
notice. Whitespace is compared loosely, so what is pinned is the names, not the
line breaks they happen to wrap at. -/

/--
info: 'Scidonia.FracPerm.StateVar.RefCount.not_exclusive_incRefN_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_exclusive_incRefN_one

/--
info: 'Scidonia.FracPerm.StateVar.RefCount.decRef_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decRef_two

/--
info: 'Scidonia.FracPerm.StateVar.RefCount.not_exclusive_of_isMt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_exclusive_of_isMt

/--
info: 'Scidonia.FracPerm.StateVar.RefCount.markMtRc_not_exclusive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms markMtRc_not_exclusive

/--
info: 'Scidonia.FracPerm.StateVar.RefCount.not_exclusive_of_neverFreed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_exclusive_of_neverFreed

/--
info: 'Scidonia.FracPerm.StateVar.RefCount.takeOut_refCount_eq_one' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms takeOut_refCount_eq_one

end ScidoniaTest.Count
