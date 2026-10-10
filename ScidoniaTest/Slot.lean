/-
Compile-time checks for the description-indexed slot
(`Scidonia.FracPerm.StateVar.Slot`).

These live in the check library, so they see exactly what a client sees. Three
kinds of control appear here, in the style of `ScidoniaTest/StateVar.lean`:

* The **correspondence's** controls are computations and theorems: the two
  inverse laws at concrete slots, including a payload too large for a machine
  word, the encoding of each summand, and `lifted_iff` used in both directions.
* The **instance's** controls are the class's operations on slots and the
  theorems that read them back: a read-after-replace at `full 9`, a slot's read
  being the slot itself, and the read–write–read snapshot at `full 7` → `full 9`
  with the old value exposed, plus the `empty → full n → empty` shape change.
* The **detector's** controls are the positive and negative pair around the
  no-reference predicate: the encoding of a payload is detached from root 0,
  and the location at root 0 is *not*, so a passing `NoRef` is not vacuous.

The last section prints the axioms of representative theorems, so that an
inherited kernel principle can be told from a new assumption.
-/
import Scidonia.FracPerm

open Scidonia.FracPerm.StateVar

namespace ScidoniaTest.Slot

/-! ## Running the correspondence

`check` fails the build when a run's value is not the expected one. -/

/-- Fail the elaboration unless `observed` is `expected`. -/
def check {α : Type} [BEq α] [Repr α] (name : String) (expected observed : α) : IO Unit := do
  unless expected == observed do
    throw (IO.userError s!"{name}: expected {repr expected}, observed {repr observed}")

/- The two inverse laws at concrete slots, including a payload of two hundred
binary digits: the payload is a `Nat`, so it is neither truncated nor rounded. -/
#eval do
  check "empty decodes from its encoding" Slot.empty (decode (encode Slot.empty))
  check "full 7 decodes from its encoding" (Slot.full 7) (decode (encode (Slot.full 7)))
  check "a large payload decodes from its encoding"
    (Slot.full (2 ^ 200)) (decode (encode (Slot.full (2 ^ 200))))

/-- The encoding of `empty` is the left summand's unit, and the encoding of
`full n` the right summand's natural: the slot's two shapes are the
description's two summands. -/
example : encode Slot.empty = Sum.inl () ∧ encode (Slot.full 7) = Sum.inr 7 :=
  ⟨rfl, rfl⟩

/-- The inverse law quantified over every slot, for arbitrary payloads. -/
example : ∀ s : Slot, decode (encode s) = s := decode_encode

/-- The inverse law quantified over every element of the description. -/
example : ∀ r : El slotDesc, encode (decode r) = r := encode_decode

/-! ## The transported instance, from outside the library

The class's operations on slots and the theorems that read them back. -/

/- The class's operations on slots, checked against their expected values: the
expected value's type fixes the operation's result type, so the class's indexed
results do not have to be named. -/
#eval do
  check "a slot read" (Slot.full 7) (LawfulStateVar.observe () (Slot.full 7))
  check "a slot replace" ((Slot.full 9, true) : Slot × Bool)
    (LawfulStateVar.replace (Slot.full 9) (Slot.full 7))

/-- Reading a slot after replacing it with `full 9` yields `full 9`. -/
example : LawfulStateVar.observe ()
    (LawfulStateVar.replace (Slot.full 9) (Slot.full 7)).1 = Slot.full 9 :=
  slot_read_after_replace (Slot.full 7) (Slot.full 9)

/-- The same read-after-replace at a large payload: the replacement is a `Nat`
and is read back exactly. -/
example : LawfulStateVar.observe ()
    (LawfulStateVar.replace (Slot.full (2 ^ 200)) Slot.empty).1 = Slot.full (2 ^ 200) :=
  slot_read_after_replace Slot.empty (Slot.full (2 ^ 200))

/-- A slot's payload survives the encoding for every natural. -/
example (n : Nat) : decode (encode (Slot.full n)) = Slot.full n :=
  slot_full_round_trip n

/-! ## Reading a slot's properties off its encoding

`lifted_iff` used in both directions: a predicate true of a slot is true of its
encoding, and a predicate false of a slot is false of its encoding; the second
direction is what makes the equivalence non-trivial (it is not `Iff.rfl` at an
arbitrary slot). -/

/-- A predicate true of `full 7` is true of `decode (encode (full 7))`. -/
example : (fun s : Slot => s = Slot.full 7) (Slot.full 7) ↔
    (fun s : Slot => s = Slot.full 7) (decode (encode (Slot.full 7))) :=
  lifted_iff (fun s => s = Slot.full 7) (Slot.full 7)

/-- A predicate *false* of `empty` is false of `decode (encode empty)`; the
right operand is the encoded one, so the equivalence moves a property in both
directions. -/
example : ¬ (fun s : Slot => s = Slot.full 9) Slot.empty ↔
    ¬ (fun s : Slot => s = Slot.full 9) (decode (encode Slot.empty)) :=
  lifted_iff (fun s : Slot => ¬ s = Slot.full 9) Slot.empty

/-! ## The no-reference law, positively and negatively

The encoding never produces a location, so the detector accepts it; the
detector's own negative control shows it is not vacuous. -/

/-- The encoding of a payload is detached from root 0. -/
example : NoRef 0 (encodeEl slotDesc (Sum.inr 5)) := trivial

/-- The encoding of the unit summand is detached from root 0. -/
example : NoRef 0 (encodeEl slotDesc (Sum.inl ())) := trivial

/-- The detector's own negative control: the location at root 0 is *not*
detached from root 0, so the passing `NoRef` above is not vacuous. -/
example : ¬ NoRef 0 (Value.loc 0) := not_noRef_loc_self 0

/-! ## The heap: the snapshot and the shape change

A client-side heap: root 0 holds `full 7`, every other cell nothing. -/

/-- The heap before the demo write: root 0 holds `full 7`. -/
def demoSlotHeap : Heap Slot := fun ℓ => if ℓ = 0 then some (Slot.full 7) else none

/-- The heap after the demo write of `full 9` at root 0. -/
def demoSlotHeap' : Heap Slot := Heap.update demoSlotHeap 0 (some (Slot.full 9))

/-- The pre-write read observes `full 7`. -/
example : ReadAt slotStateVar 0 () demoSlotHeap demoSlotHeap (Slot.full 7) :=
  ⟨Slot.full 7, by simp [At, demoSlotHeap], trivial, rfl,
    (slot_observe_eq (Slot.full 7)).symm⟩

/-- The write installs `full 9` at root 0 and reports that it took effect. -/
example : WriteAt slotStateVar 0 (Slot.full 9) demoSlotHeap demoSlotHeap' true :=
  ⟨Slot.full 7, by simp [At, demoSlotHeap], trivial, rfl, rfl⟩

/-- The post-write cell holds `full 9`. -/
example : At 0 (Slot.full 9) demoSlotHeap' := by
  show demoSlotHeap' 0 = some (Slot.full 9)
  rw [demoSlotHeap', Heap.update_self]

/-- The snapshot at `full 7` → `full 9`: the pre-write observation `full 7` is
bound to the pre-write cell, the post-write cell holds `full 9`, and the old
`full 7` is still the value the pre-write heap holds. -/
example : ReadAt slotStateVar 0 () demoSlotHeap demoSlotHeap (Slot.full 7) ∧
    At 0 (Slot.full 9) demoSlotHeap' ∧ At 0 (Slot.full 7) demoSlotHeap :=
  slot_snapshot_full7_full9
    (by simp [At, demoSlotHeap])
    ⟨Slot.full 7, by simp [At, demoSlotHeap], trivial, rfl, rfl⟩

/-- The same snapshot through M2's *generic* `snapshot_after_write`, at the slot
instance: the old observation and the new one are tied to the pre-write and
post-write cells, not to positions in a trace. This theorem is not re-proved for
the slot — it is the generic one. -/
example : ∃ s, At 0 s demoSlotHeap ∧
    (Slot.full 7) = LawfulStateVar.observe () s ∧
    (Slot.full 9) = LawfulStateVar.observe () (LawfulStateVar.replace (Slot.full 9) s).1 := by
  have hr : ReadAt slotStateVar 0 () demoSlotHeap demoSlotHeap (Slot.full 7) :=
    ⟨Slot.full 7, by simp [At, demoSlotHeap], trivial, rfl,
      (slot_observe_eq (Slot.full 7)).symm⟩
  have hw : WriteAt slotStateVar 0 (Slot.full 9) demoSlotHeap demoSlotHeap' true :=
    ⟨Slot.full 7, by simp [At, demoSlotHeap], trivial, rfl, rfl⟩
  have hr' : ReadAt slotStateVar 0 () demoSlotHeap' demoSlotHeap' (Slot.full 9) :=
    ⟨Slot.full 9, by
        show demoSlotHeap' 0 = some (Slot.full 9)
        rw [demoSlotHeap', Heap.update_self], trivial, rfl,
      (slot_observe_eq (Slot.full 9)).symm⟩
  exact snapshot_after_write hr hw hr'

/-! ### The shape change on one root cell

Root 0 goes `empty → full 5 → empty`. -/

/-- The heap holding an empty slot at root 0. -/
def shapeHeap₀ : Heap Slot := fun ℓ => if ℓ = 0 then some Slot.empty else none

/-- The heap after installing `full 5` at root 0. -/
def shapeHeap₁ : Heap Slot := Heap.update shapeHeap₀ 0 (some (Slot.full 5))

/-- The heap after installing `empty` again at root 0. -/
def shapeHeap₂ : Heap Slot := Heap.update shapeHeap₁ 0 (some Slot.empty)

/-- The shape change `empty → full 5 → empty` on root 0, with both replacements
reporting `true` and the original `empty` still the value of the first heap. -/
example : At 0 Slot.empty shapeHeap₀ ∧ At 0 (Slot.full 5) shapeHeap₁ ∧
    At 0 Slot.empty shapeHeap₂ := by
  have h0 : At 0 Slot.empty shapeHeap₀ := by simp [At, shapeHeap₀]
  have hcell₁ : At 0 (Slot.full 5) shapeHeap₁ := by
    show shapeHeap₁ 0 = some (Slot.full 5)
    rw [shapeHeap₁, Heap.update_self]
  have hcell₂ : At 0 Slot.empty shapeHeap₂ := by
    show shapeHeap₂ 0 = some Slot.empty
    rw [shapeHeap₂, Heap.update_self]
  have hw1 : WriteAt slotStateVar 0 (Slot.full 5) shapeHeap₀ shapeHeap₁ true :=
    ⟨Slot.empty, h0, trivial, rfl, rfl⟩
  have hw2 : WriteAt slotStateVar 0 Slot.empty shapeHeap₁ shapeHeap₂ true :=
    ⟨Slot.full 5, hcell₁, trivial, rfl, rfl⟩
  have h := slot_shape_change 5 h0 hw1 hw2
  exact ⟨h.2.2.2.2, h.2.2.1, h.2.2.2.1⟩

/-! ## Axioms of representative theorems

Only the standard kernel principles — `propext`, `Classical.choice`,
`Quot.sound` — may appear; a name of this development appearing here would be a
new assumption. -/

#print axioms Scidonia.FracPerm.StateVar.decode_encode
#print axioms Scidonia.FracPerm.StateVar.encode_decode
#print axioms Scidonia.FracPerm.StateVar.lifted_iff
#print axioms Scidonia.FracPerm.StateVar.encodeEl_injective
#print axioms Scidonia.FracPerm.StateVar.encodeEl_noRef
#print axioms Scidonia.FracPerm.StateVar.slot_observe_eq
#print axioms Scidonia.FracPerm.StateVar.slot_read_after_replace
#print axioms Scidonia.FracPerm.StateVar.slot_snapshot_full7_full9
#print axioms Scidonia.FracPerm.StateVar.slot_shape_change
#print axioms Scidonia.FracPerm.StateVar.slot_full_round_trip

end ScidoniaTest.Slot
