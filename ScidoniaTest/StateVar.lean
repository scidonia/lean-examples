/-
Compile-time checks for the generic state-variable interface
`Scidonia.FracPerm.StateVar`.

These live in the check library, so they see exactly what a client sees. The
interface's rules are of three kinds here:

* The **witness's** rules are behavioural, so their controls are computations and
  theorems at the array instance: the class's operations on an array, the
  instance-specific bounds and size lemmas, and a run of the shipped runner.
* The **model's** rules are semantic, and their controls are theorems: a
  concrete fork run in the order *opposite* to the sequential denotation reaches
  the denotation's value, a heap read–write–read snapshot ties the two
  observations to their cells, the translation bridges agree with the structured
  denotations, and the frame and half-share lemmas hold at concrete operands.
* The **laws'** controls are negative, and they are theorems stating that a
  specific obligation of a specific *countermodel* is false — a proposition, not
  a tactic failure — paired with the affirmative array witness. A pinned
  `#guard_msgs` shows the countermodel's instance failing to elaborate.

The last section prints the axioms of representative theorems, so that an
inherited kernel principle can be told from a new assumption.
-/
import Scidonia.FracPerm

open Scidonia.FracPerm.StateVar

namespace ScidoniaTest.StateVar

/-! ## Running the protocol

`check` fails the build when a run's value is not the expected one. -/

/-- Fail the elaboration unless `observed` is `expected`. -/
def check {α : Type} [BEq α] [Repr α] (name : String) (expected observed : α) : IO Unit := do
  unless expected == observed do
    throw (IO.userError s!"{name}: expected {repr expected}, observed {repr observed}")

/-! ## The array witness, from outside the library

The class's operations on the demo array, the demo tree, and the shipped runner.
The ascriptions on the guarded terms are what a client needs to name the
instance's result types: the class's operations are indexed by the instance, and
a numeral or a `BEq` has to be told which of them it is at. -/

/-- The array the witness checks run on: two elements, so an in-bounds and an
out-of-bounds index are both available. -/
def demoArray : Array UInt64 := #[7, 8]

/- The class's operations on the demo array, from outside the library: each run
is checked against its expected value, and `check` throws when they differ. The
expected value's type fixes the operation's result type, so the class's indexed
results do not have to be named. -/
#eval do
  check "the element read" (some 7) (LawfulStateVar.observe (.get 0) demoArray)
  check "an out-of-bounds element read" (none : Option UInt64)
    (LawfulStateVar.observe (.get 9) demoArray)
  check "the size observation" (2 : Nat) (LawfulStateVar.observe (ArrayReadOp.size) demoArray)
  check "an in-bounds write" ((#[9, 8], true) : Array UInt64 × Bool)
    (LawfulStateVar.replace (0, 9) demoArray)
  check "an out-of-bounds write" ((#[7, 8], false) : Array UInt64 × Bool)
    (LawfulStateVar.replace (9, 9) demoArray)

/-- An array write preserves the array's size. -/
example : (LawfulStateVar.replace (0, 9) demoArray).1.size = demoArray.size :=
  arrayReplace_size demoArray (0, 9)

/-- An array write reports `true` exactly when the index is in bounds. -/
example : (LawfulStateVar.replace (0, 9) demoArray).2 = true ↔ 0 < demoArray.size :=
  arrayReplace_bounds demoArray (0, 9)

/- The shipped runner still runs, and its value is the one the protocol
computes. -/
#eval do
  check "the shipped runner still runs" true
    (← Scidonia.FracPerm.Structured.runFresh { size := 4, fill := 7 }
      (Scidonia.FracPerm.Structured.Program.set 0 9))

/-! ## The no-reference law, positively and negatively

A positive control for the detector: `NoRef` refuses the location it is given,
and accepts an encoded element or size observation. -/

/-- An encoded element observation is detached from root 0. -/
example : NoRef 0 (encodeArrayRead (.get 0) (some 7)) := trivial

/-- An encoded size observation is detached from root 0. -/
example : NoRef 0 (encodeArrayRead .size (2 : Nat)) := trivial

/-- The detector's own negative control: the location at root 0 is *not*
detached from root 0, so a passing `NoRef` above is not vacuous. -/
example : ¬ NoRef 0 (Value.loc 0) := not_noRef_loc_self 0

/-! ## The model at the array instance

A concrete fork, run in the order opposite to the sequential denotation's. -/

/-- A client's read tree: the element at 0 and the size, as a fork of the two
branches below. -/
def demoLeft : RTree ArrayReadOp ArrayResult (Option UInt64) :=
  .read (.get 0) (fun o => .pure o)

/-- The fork's right branch: the size. -/
def demoRight : RTree ArrayReadOp ArrayResult Nat :=
  .read .size (fun n => .pure n)

/-- The fork's continuation: pair the branches' results. -/
def demoJoin : Option UInt64 × Nat → RTree ArrayReadOp ArrayResult (Option UInt64 × Nat) :=
  fun p => .pure p

/-- The demo tree: a fork of the two branches above. -/
def demoTree : RTree ArrayReadOp ArrayResult (Option UInt64 × Nat) :=
  .fork demoLeft demoRight demoJoin

/- The sequential denotation of the demo tree. -/
#guard (val demoArray demoTree : Option UInt64 × Nat) == (some 7, 2)

/-- The demo fork run *right branch first*: the interleaving the sequential
denotation does not use, reaching the same finished run. -/
theorem demoRunRightFirst :
    StepStar arrayStateVar demoArray (.run 1 demoTree) (.run 1 (.pure (some 7, 2))) := by
  have hfork : Step arrayStateVar demoArray (.run 1 demoTree)
      (.wait 1 (.run (1 / 2) demoLeft) (.run (1 / 2) demoRight) demoJoin) := by
    unfold demoTree
    exact Step.fork
  have hright : Step arrayStateVar demoArray
      (.wait 1 (.run (1 / 2) demoLeft) (.run (1 / 2) demoRight) demoJoin)
      (.wait 1 (.run (1 / 2) demoLeft) (.run (1 / 2) (.pure 2)) demoJoin) := by
    simp only [arrayStateVar, demoRight, demoArray]
    exact Step.right Step.read
  have hleft : Step arrayStateVar demoArray
      (.wait 1 (.run (1 / 2) demoLeft) (.run (1 / 2) (.pure 2)) demoJoin)
      (.wait 1 (.run (1 / 2) (.pure (some 7))) (.run (1 / 2) (.pure 2)) demoJoin) := by
    simp only [arrayStateVar, demoLeft, demoArray]
    exact Step.left Step.read
  have hjoin : Step arrayStateVar demoArray
      (.wait 1 (.run (1 / 2) (.pure (some 7))) (.run (1 / 2) (.pure 2)) demoJoin)
      (.run 1 (.pure (some 7, 2))) := by
    unfold demoJoin
    exact Step.join
  exact .tail (.tail (.tail (.tail (.refl _) hfork) hright) hleft) hjoin

/-- Every interleaving computes the sequential denotation's value: the
right-first run above computes `(some 7, 2)`. -/
example : (some 7, 2) = val demoArray demoTree :=
  complete_run_value demoRunRightFirst

/-- The demo fork's read phase is well formed at share `1`, and a well-formed
reading configuration's readers hold the whole share. -/
example : WFConf arrayStateVar (.reading demoArray (.run 1 demoTree)
    (fun _ => PTree.pure true)) := by
  refine ⟨trivial, ⟨rfl, ?_⟩, ?_⟩
  · unfold demoTree demoLeft demoRight demoJoin
    exact ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial⟩
  · intro a
    trivial

/-- The readers of that configuration hold the whole share. -/
example : leafSum arrayStateVar (.run 1 demoTree) = 1 := by
  have hw : WFConf arrayStateVar (.reading demoArray (.run 1 demoTree)
      (fun _ => PTree.pure true)) := by
    refine ⟨trivial, ⟨rfl, ?_⟩, ?_⟩
    · unfold demoTree demoLeft demoRight demoJoin
      exact ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial⟩
    · intro a
      trivial
  exact reading_share_is_one (inst := arrayStateVar) hw

/-! ## The heap: frame, and the read–write–read snapshot -/

/-- A client-side heap: root 0 holds the demo array, every other cell nothing. -/
def demoHeap : Heap (Array UInt64) := fun ℓ => if ℓ = 0 then some demoArray else none

/-- The heap after the demo write of 9 at index 0. -/
def demoHeap' : Heap (Array UInt64) :=
  Heap.update demoHeap 0 (some (arrayReplace (0, 9) demoArray).1)

/-- A write leaves another cell alone: the frame lemma at concrete roots. -/
example (h : Heap (Array UInt64)) : Heap.update h 4 (some #[1]) 9 = h 9 :=
  Heap.update_of_ne (by decide) _

/-- Reading the root before the write observes 7. -/
example : ReadAt arrayStateVar 0 (.get 0) demoHeap demoHeap (some 7) :=
  ⟨demoArray, by simp [At, demoHeap], trivial, rfl, rfl⟩

/-- Writing 9 at index 0 is a `WriteAt` of the root cell, reporting `true`. -/
example : WriteAt arrayStateVar 0 (0, 9) demoHeap demoHeap' true :=
  ⟨demoArray, by simp [At, demoHeap], trivial, rfl, rfl⟩

/-- Reading the root after the write observes 9. -/
example : ReadAt arrayStateVar 0 (.get 0) demoHeap' demoHeap' (some 9) :=
  ⟨(arrayReplace (0, 9) demoArray).1,
    by simp [At, demoHeap', Heap.update], trivial, rfl, rfl⟩

/-- The snapshot theorem at the client: the pre-write observation 7 and the
post-write observation 9 are bound to the *same* cell, before and after its
replacement, not merely to positions in a trace. -/
example : ∃ s, At 0 s demoHeap ∧ (some 7) = LawfulStateVar.observe (.get 0) s ∧
    (some 9) = LawfulStateVar.observe (.get 0) (LawfulStateVar.replace (0, 9) s).1 := by
  have hr : ReadAt arrayStateVar 0 (.get 0) demoHeap demoHeap (some 7) :=
    ⟨demoArray, by simp [At, demoHeap], trivial, rfl, rfl⟩
  have hw : WriteAt arrayStateVar 0 (0, 9) demoHeap demoHeap' true :=
    ⟨demoArray, by simp [At, demoHeap], trivial, rfl, rfl⟩
  have hr' : ReadAt arrayStateVar 0 (.get 0) demoHeap' demoHeap' (some 9) :=
    ⟨(arrayReplace (0, 9) demoArray).1,
      by simp [At, demoHeap', Heap.update], trivial, rfl, rfl⟩
  exact snapshot_after_write hr hw hr'

/-- The heap read transition and the model's `read` step agree: reading the root
that holds the array is a read step of the array. -/
example : Step arrayStateVar demoArray
    (.run 1 (.read (.get 0) (fun (o : Option UInt64) => .pure o)))
    (.run 1 (.pure (some 7))) :=
  readAt_step_observe (inst := arrayStateVar) (ℓ := 0) (s := demoArray)
    (h := demoHeap) (h' := demoHeap) (v := some 7) (o := .get 0)
    (k := fun o => .pure o)
    (hat := by simp [At, demoHeap])
    (hr := ⟨demoArray, by simp [At, demoHeap], trivial, rfl, rfl⟩)

/-! ## Shares -/

/-- Halving the whole share gives a valid half. -/
example : ValidShare ((1 : Rat) / 2) := half_valid ⟨by grind, by grind⟩

/-- Rejoining two halves restores the whole. -/
example : (1 : Rat) / 2 + 1 / 2 = 1 := halves_rejoin 1

/-- A full share admits no further reader. -/
example : ¬ (1 + (1 / 2 : Rat) ≤ 1) := cannot_add_reader (1 / 2) (by grind)

/-! ## The bridge to the structured interface -/

/- The generic denotation of a translated structured reader is the structured
denotation, computed here on the same array. -/
#guard (val demoArray (liftR (Scidonia.FracPerm.Structured.Reader.treeOf
  (Scidonia.FracPerm.Structured.Reader.get 0))) : Option UInt64) == some 7

/- The same for a structured program: the translated tree's generic denotation
is the structured one, and the write reports `true`. -/
#guard (pval demoArray (liftP (Scidonia.FracPerm.Structured.Program.treeOf
  (Scidonia.FracPerm.Structured.Program.set 0 9))) : Bool) == true

/-- The bridge value theorem, stated as an equation for a client. -/
example : val demoArray
    (liftR (Scidonia.FracPerm.Structured.Reader.treeOf
      (Scidonia.FracPerm.Structured.Reader.get 0))) =
      Scidonia.FracPerm.Structured.val demoArray
        (Scidonia.FracPerm.Structured.Reader.treeOf
          (Scidonia.FracPerm.Structured.Reader.get 0)) :=
  bridge_val demoArray _

/-- The bridge program theorem, stated as an equation for a client. -/
example : pval demoArray
    (liftP (Scidonia.FracPerm.Structured.Program.treeOf
      (Scidonia.FracPerm.Structured.Program.set 0 9))) =
      Scidonia.FracPerm.Structured.pval demoArray
        (Scidonia.FracPerm.Structured.Program.treeOf
          (Scidonia.FracPerm.Structured.Program.set 0 9)) :=
  bridge_pval demoArray _

/-- `runFresh_eq_pval` at a concrete program: the runner's value is the generic
denotation of the lifted tree against the array the runner creates. -/
example : Scidonia.FracPerm.Structured.runFresh { size := 4, fill := 7 }
    (Scidonia.FracPerm.Structured.Program.set 0 9) = (do
      let a : Array UInt64 := LawfulStateVar.initial { size := 4, fill := 7 }
      return pval a (liftP (Scidonia.FracPerm.Structured.Program.treeOf
        (Scidonia.FracPerm.Structured.Program.set 0 9)))) :=
  runFresh_eq_pval { size := 4, fill := 7 } _

/-! ## Negative controls

Each is a proposition about a countermodel's obligation, and each is *false* of
that countermodel — so a law is not vacuous, and a proof of it is not a proof of
anything. The array witness above discharges the same obligations.

The read countermodel: the state is a `Nat`, a read returns the state itself as
a location, and the encoding is the identity. -/

/-- Observing countermodel state `s` names the root at `s`, so the no-reference
obligation is false for it (witnesses `ℓ = s = 0`). -/
theorem bad_read_rejected : ¬ (∀ (ℓ s : Nat), NoRef ℓ (Value.loc s)) := by
  intro h
  exact (h 0 0) rfl

/-- The write countermodel: valid states are `0`, and the replacement adds one,
so admissibility is not closed under replacement (witness `s = 0`). -/
theorem bad_write_rejected : ¬ (∀ s : Nat, s = 0 → (s + 1) = 0) := by
  intro h
  exact absurd (h 0 rfl) (by decide)

/-- The encoding countermodel: a constant encoding cannot distinguish results,
so injectivity is false for it (witnesses `true` and `false`). -/
theorem bad_encode_rejected : ¬ (∀ x y : Bool, (Value.unit : Value) = Value.unit → x = y) := by
  intro h
  exact absurd (h true false rfl) (by decide)

/- The same read countermodel as a class instance. Its `observe_detached` field
cannot be supplied, and the attempt fails for the reason the theorem above
states: the obligation is `s ≠ ℓ`, which `trivial` is not. -/
/--
error: Type mismatch
  trivial
has type
  True
but is expected to have type
  NoRef ℓ (Value.loc s)
-/
#guard_msgs in
example : LawfulStateVar Nat Unit Unit Unit where
  Result _ := Value
  initial _ := 0
  Valid _ := True
  observe _ s := .loc s
  replace _ s := (s, true)
  encodeRead _ v := v
  initial_valid _ := trivial
  replace_valid _ _ _ := trivial
  encodeRead_injective := fun _ _ _ h => h
  observe_detached := fun ℓ _ s _ => trivial

/-! ## Axioms of representative theorems

Only the standard kernel principles — `propext`, `Classical.choice`,
`Quot.sound` — may appear; a name of this development appearing here would be a
new assumption. -/

/- The detector's affirmative control: a theorem that rests on nothing prints
that it depends on no axioms, so the standard-principles lines above are a
result about those theorems and not a constant output. -/
#print axioms Scidonia.FracPerm.StateVar.encodeArrayRead_injective
#print axioms Scidonia.FracPerm.StateVar.read_agreement

#print axioms Scidonia.FracPerm.StateVar.eval_unique
#print axioms Scidonia.FracPerm.StateVar.replay_trace
#print axioms Scidonia.FracPerm.StateVar.pstep_wf
#print axioms Scidonia.FracPerm.StateVar.safe_result
#print axioms Scidonia.FracPerm.StateVar.snapshot_after_write
#print axioms Scidonia.FracPerm.StateVar.bridge_val
#print axioms Scidonia.FracPerm.StateVar.bridge_pval
#print axioms Scidonia.FracPerm.StateVar.runFresh_eq_pval

end ScidoniaTest.StateVar
