/-
A worked description-indexed state variable: a slot, encoded against the
description `slotDesc` and made lawful by the universe instance's transport.

A `Slot` is `empty`, or `full value` for a natural payload. It is the type of a
state variable that is a single cell: the slot is *not* a generic recursive
layout, and its lawful witness is *not* proved from nothing.

The construction has two halves, and neither proves a law of the slot's own.

* The description half is `El slotDesc` — `Sum Unit Nat` — and it is *general*:
  `Scidonia.FracPerm.StateVar.Universe` proves one instance for every
  description, with `encodeEl`'s injectivity and its no-reference law obtained
  by a single structural induction on the description. Nothing in it mentions
  `Slot`.
* The slot-specific half is `Slot`, `encode`, `decode`, the two inverse laws
  `decode_encode`/`encode_decode`, and the instance below. The instance is
  `transport slotDesc Slot encode decode decode_encode encode_decode`: each of
  its operations is the universe instance's conjugated by the isomorphism, and
  each of its law fields is the corresponding universe law after an inverse law
  cancels the conjugation — never a fresh proof of the slot's own.

`lifted_iff` is the consequence of `decode_encode` a client reads off: a
predicate on slots holds of `s` exactly when it holds of `decode (encode s)`.
`slot_read_after_replace` reads a slot back after replacing it, and
`slot_snapshot_full7_full9` is the read–write–read snapshot at `full 7` →
`full 9`, with the old value still the value the pre-write heap holds.
`slot_shape_change` exercises the `empty → full n → empty` shape change on one
root cell, and `slot_full_round_trip`/`slot_read_after_replace_full` exercise a
payload of arbitrary size.

The replacement is *logical*: a write yields a new heap value and destroys
nothing (`Scidonia.FracPerm.StateVar.Heap`), so this is not physical
fixed-node mutation. There is no `IO.Ref`, no C, no foreign backend, no
independent resource algebra and no new run-time in-place claim; the heap the
snapshot theorems use is the model's single-root logical heap, and the array's
in-place evidence stays the `inplace` harness.
-/
import Scidonia.FracPerm.StateVar.Description
import Scidonia.FracPerm.StateVar.Universe

namespace Scidonia.FracPerm.StateVar

/-! ## The slot and its encoding -/

/-- A slot: empty, or holding a natural payload. -/
inductive Slot where
  /-- The empty slot. -/
  | empty
  /-- A slot holding `value`. -/
  | full (value : Nat)
deriving DecidableEq, Repr

/-- Encode a slot as the description's element: `empty` is the left summand's
unit, `full n` the right summand's natural. -/
def encode : Slot → El slotDesc
  | .empty => Sum.inl ()
  | .full n => Sum.inr n

/-- Decode the description's element back to a slot. -/
def decode : El slotDesc → Slot
  | Sum.inl _ => .empty
  | Sum.inr n => .full n

/-- One inverse law: decoding an encoded slot is the slot itself. The proof is a
case per constructor of `Slot`. -/
theorem decode_encode (s : Slot) : decode (encode s) = s := by
  cases s <;> rfl

/-- The other inverse law: encoding a decoded element is the element itself.
The proof is a case per constructor of `El slotDesc`; the left summand's `Unit`
has one element, so that case collapses too. -/
theorem encode_decode (r : El slotDesc) : encode (decode r) = r := by
  obtain (u | n) := r
  · cases u; rfl
  · rfl

/-- A predicate on slots transports along the inverse law: it holds of `s`
exactly when it holds of `decode (encode s)`. This is `decode_encode` read as an
equivalence, and it is the statement a client uses to move a property between a
slot and its encoding. -/
theorem lifted_iff (P : Slot → Prop) (s : Slot) : P s ↔ P (decode (encode s)) := by
  rw [decode_encode s]

/-! ## The instance, transported from the universe instance

`encode` and `decode` are the isomorphism between `Slot` and `El slotDesc`, and
the two inverse laws are what `transport` needs. The slot's operations are the
universe instance's carried along them, and the law fields are the universe
instance's laws after an inverse law cancels the conjugation. -/

/-- The slot as a lawful state variable, transported from the single universe
instance at `slotDesc` across `encode` and `decode` rather than proved from
nothing.

A state is a `Slot`, initialized from a `Slot`; the read operation is `Unit` and
returns the state, the write operation is the `Slot` to install, and a write
always takes effect (`true`). -/
instance slotStateVar : LawfulStateVar Slot Slot Unit Slot :=
  transport slotDesc Slot encode decode decode_encode encode_decode

/-! ## The slot's facts

Each is the corresponding transported statement at this isomorphism; none is
proved by a case analysis of its own. -/

/-- The slot instance's `initial` is the slot itself. -/
theorem slot_initial_eq (s : Slot) : LawfulStateVar.initial s = s :=
  transport_initial_self slotDesc Slot encode decode decode_encode encode_decode s

/-- Reading a slot yields the slot. -/
theorem slot_observe_eq (s : Slot) : LawfulStateVar.observe () s = s :=
  transport_observe_self slotDesc Slot encode decode decode_encode encode_decode s

/-- Replacing a slot with `new` yields `new` and reports `true`. -/
theorem slot_replace_eq (new current : Slot) :
    LawfulStateVar.replace new current = (new, true) :=
  transport_replace_self slotDesc Slot encode decode decode_encode encode_decode new current

/-- The slot's read encoding is the general `encodeEl` at `encode`: the slot's
own encoding adds nothing to the description's. The instance is named because
`encodeRead`'s argument type is itself a projection of the instance, so it
cannot be inferred from the argument alone. -/
theorem slotEncodeRead_eq (s : Slot) :
    (slotStateVar : LawfulStateVar Slot Slot Unit Slot).encodeRead () s =
      encodeEl slotDesc (encode s) :=
  transport_encodeRead_eq slotDesc Slot encode decode decode_encode encode_decode s

/-- Reading a slot after replacing it with `t` yields `t`: the transported
read-after-replace, which uses both inverse laws. -/
theorem slot_read_after_replace (s t : Slot) :
    LawfulStateVar.observe () (LawfulStateVar.replace t s).1 = t :=
  transport_read_after_replace slotDesc Slot encode decode decode_encode encode_decode s t

/-- The read–write–read snapshot at the slot instance, at `full 9`: the first
read's value is bound to the *pre-write* cell and the second read's to the
*post-write* cell, exactly as `snapshot_after_write` states it generically. This
is M2's generic theorem at `slotStateVar`, not a slot-specific proof. -/
theorem slot_snapshot_after_write {ℓ : Loc} {h h' : Heap Slot} {b : Bool}
    {v v' : Slot} (hr : ReadAt slotStateVar ℓ () h h v)
    (hw : WriteAt slotStateVar ℓ (Slot.full 9) h h' b)
    (hr' : ReadAt slotStateVar ℓ () h' h' v') :
    ∃ s, At ℓ s h ∧ v = LawfulStateVar.observe () s ∧
      v' = LawfulStateVar.observe () (LawfulStateVar.replace (Slot.full 9) s).1 :=
  snapshot_after_write hr hw hr'

/-- The concrete snapshot: root `ℓ` holds `full 7`, the write installs
`full 9`, and then the pre-write read observes `full 7`, the post-write cell
holds `full 9`, and the old `full 7` is still what the pre-write heap holds —
a write produces a new heap and destroys nothing, so the pre-write cell keeps
its value. -/
theorem slot_snapshot_full7_full9 {ℓ : Loc} {h h' : Heap Slot}
    (hat : At ℓ (Slot.full 7) h)
    (hw : WriteAt slotStateVar ℓ (Slot.full 9) h h' true) :
    ReadAt slotStateVar ℓ () h h (Slot.full 7) ∧ At ℓ (Slot.full 9) h' ∧
      At ℓ (Slot.full 7) h := by
  refine ⟨⟨Slot.full 7, hat, trivial, rfl, (slot_observe_eq (Slot.full 7)).symm⟩, ?_, hat⟩
  obtain ⟨s, hat₀, _, hh', _⟩ := hw
  have hs : s = Slot.full 7 := read_agreement hat₀ hat
  rw [hs] at hh'
  show h' ℓ = some (Slot.full 9)
  rw [hh', Heap.update_self, slot_replace_eq (Slot.full 9) (Slot.full 7)]

/-- The shape change `empty → full n → empty` on one root cell: from a cell
holding `empty`, installing `full n` makes the cell hold `full n`, installing
`empty` again makes it hold `empty` again, and both replacements reported
`true`. The `empty` the cell started with is still the value of the pre-write
heap. -/
theorem slot_shape_change (n : Nat) {ℓ : Loc} {h₀ h₁ h₂ : Heap Slot} {b c : Bool}
    (h0 : At ℓ Slot.empty h₀)
    (hw1 : WriteAt slotStateVar ℓ (Slot.full n) h₀ h₁ b)
    (hw2 : WriteAt slotStateVar ℓ Slot.empty h₁ h₂ c) :
    b = true ∧ c = true ∧ At ℓ (Slot.full n) h₁ ∧ At ℓ Slot.empty h₂ ∧
      At ℓ Slot.empty h₀ := by
  obtain ⟨s₁, hat₁, _, hh1, hb1⟩ := hw1
  obtain ⟨s₂, hat₂, _, hh2, hc2⟩ := hw2
  have hs₁ : s₁ = Slot.empty := read_agreement hat₁ h0
  rw [hs₁] at hh1 hb1
  have hcell₁ : At ℓ (Slot.full n) h₁ := by
    show h₁ ℓ = some (Slot.full n)
    rw [hh1, Heap.update_self, slot_replace_eq (Slot.full n) Slot.empty]
  have hs₂ : s₂ = Slot.full n := read_agreement hat₂ hcell₁
  rw [hs₂] at hh2 hc2
  have hcell₂ : At ℓ Slot.empty h₂ := by
    show h₂ ℓ = some Slot.empty
    rw [hh2, Heap.update_self, slot_replace_eq Slot.empty (Slot.full n)]
  exact ⟨hb1, hc2, hcell₁, hcell₂, h0⟩

/-- A slot's payload survives the encoding whatever its size: `full n` decodes
back to itself for every natural, large ones included, so a payload is a number
and not a truncated field. -/
theorem slot_full_round_trip (n : Nat) : decode (encode (Slot.full n)) = Slot.full n :=
  decode_encode (Slot.full n)

/-- Reading after replacing with a large payload yields exactly that payload:
`slot_read_after_replace` at an arbitrary `n`, which is what makes the payload a
`Nat` and not a machine word. -/
theorem slot_read_after_replace_full (n : Nat) :
    LawfulStateVar.observe () (LawfulStateVar.replace (Slot.full n) Slot.empty).1 =
      Slot.full n :=
  slot_read_after_replace Slot.empty (Slot.full n)

end Scidonia.FracPerm.StateVar
