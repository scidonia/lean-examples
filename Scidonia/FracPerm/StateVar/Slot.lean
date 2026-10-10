/-
A worked description-indexed state variable: a slot, encoded against the
description `slotDesc` and made lawful by transporting the description's witness
across the two inverse laws.

A `Slot` is `empty`, or `full value` for a natural payload. It is the type of a
state variable that is a single cell: the slot is *not* a generic recursive
layout, and its lawful witness is *not* proved from nothing.

The construction has two halves.

* The description-specific half is `El slotDesc` — `Sum Unit Nat`. Its lawful
  witness is transport-ready: `encodeElSlotDesc` sends the left summand's unit to
  `.inl .unit` and the right summand's natural to `.inr (.nat n)`, and the two
  facts a transport needs are proved from those cases —
  `encodeElSlotDesc_injective` and `encodeElSlotDesc_detached`. Nothing here
  mentions `Slot`; this is the shape a proof for an arbitrary description takes
  (a general witness for an arbitrary description replaces exactly these two
  lemmas by their general form, one case per constructor of `Desc`).
* The slot-specific half is `Slot`, `encode`, `decode`, the two inverse laws
  `decode_encode`/`encode_decode`, and the transported instance below. The
  instance's `Valid`, `initial`, `observe`, `replace` and `encodeRead` are each
  written as the description instance's operation *conjugated by* `encode` and
  `decode` (`slotValid` and friends), and every law field is discharged from the
  combination of the corresponding description law and the inverse law that
  cancels the conjugation — never by a fresh proof of the slot's own.

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
import Scidonia.FracPerm.StateVar.Heap

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

/-! ## The description-specific witness

`El slotDesc` is `Sum Unit Nat`. Its encoding is a case analysis over the two
summands, and the two facts a transported witness needs are proved here — once,
from those cases, and with no mention of `Slot`. -/

/-- Encode an element of the slot description as a logical value: the left
summand's unit becomes `.inl .unit`, the right summand's natural `.inr (.nat n)`.
No other constructor is reachable, so the encoding never produces a `.loc`. -/
def encodeElSlotDesc : El slotDesc → Value
  | Sum.inl _ => .inl .unit
  | Sum.inr n => .inr (.nat n)

/-- `encodeElSlotDesc` distinguishes elements: two elements it encodes as the
same value are the same element. The `Unit` summand has one element, and the
`Nat` summand is encoded injectively; the two summands are separated by the
`.inl`/`.inr` tags. -/
theorem encodeElSlotDesc_injective : Function.Injective encodeElSlotDesc := by
  intro x y h
  obtain (u | n) := x
  · cases u
    obtain (u' | n') := y
    · cases u'; rfl
    · exact absurd h (by simp [encodeElSlotDesc])
  · obtain (u' | n') := y
    · cases u'; exact absurd h (by simp [encodeElSlotDesc])
    · have hn : n = n' := Value.nat.inj (Value.inr.inj h)
      subst hn
      rfl

/-- An element of the slot description is detached from every root: the encoding
of a unit or a natural names no `.loc`. -/
theorem encodeElSlotDesc_detached (ℓ : Loc) (d : El slotDesc) :
    NoRef ℓ (encodeElSlotDesc d) := by
  obtain (u | n) := d
  · cases u; trivial
  · trivial

/-- The description `slotDesc` as a lawful state variable, built from its
sum/unit/nat structure.

A state is an element of `El slotDesc`; the read operation is `Unit` and yields
the state itself, the write operation is the element to install, and the write
replaces unconditionally (`true`). The encoding is `encodeElSlotDesc`, so the
four laws are the two lemmas above together with the triviality of `True`
validity.

This is the witness `Slot`'s instance is transported from. A general witness for
every description states the same four laws once, and then exactly
`encodeElSlotDesc_injective` and `encodeElSlotDesc_detached` are replaced by
their general forms. -/
instance slotDescStateVar :
    LawfulStateVar (El slotDesc) (El slotDesc) Unit (El slotDesc) where
  Result _ := El slotDesc
  initial d := d
  Valid _ := True
  observe _ d := d
  replace d _ := (d, true)
  encodeRead _ d := encodeElSlotDesc d
  initial_valid _ := trivial
  replace_valid _ _ _ := trivial
  encodeRead_injective _ _ _ h := encodeElSlotDesc_injective h
  observe_detached ℓ _ d _ := encodeElSlotDesc_detached ℓ d

/-! ## Transporting the witness across `encode` and `decode`

Each operation of the `Slot` instance is the description instance's operation
conjugated by the encoding: `slotObserve () s` is `decode (observe () (encode
s))`, and so on. The conjugation is what the law fields below cancel with the
inverse laws. -/

/-- The description's validity, transported to slots. -/
def slotValid (s : Slot) : Prop :=
  slotDescStateVar.Valid (encode s)

/-- The description's `initial`, transported to slots. -/
def slotInitial (s : Slot) : Slot :=
  decode (slotDescStateVar.initial (encode s))

/-- The description's `observe`, transported to slots: observe the encoded
state and decode the result. -/
def slotObserve (_ : Unit) (s : Slot) : Slot :=
  decode (slotDescStateVar.observe () (encode s))

/-- The description's `replace`, transported to slots: encode the replacement
and the current state, replace there, and decode the resulting state. `Bool` is
the description instance's own report and is carried through unchanged. -/
def slotReplace (new current : Slot) : Slot × Bool :=
  (decode (slotDescStateVar.replace (encode new) (encode current)).1,
    (slotDescStateVar.replace (encode new) (encode current)).2)

/-- The description's `encodeRead`, transported to slots: encode the observed
value with the description's encoding. -/
def slotEncodeRead (_ : Unit) (s : Slot) : Value :=
  slotDescStateVar.encodeRead () (encode s)

/-- The transported `initial` is the slot itself: `decode_encode` cancels the
conjugation. -/
theorem slotInitial_self (s : Slot) : slotInitial s = s := by
  unfold slotInitial
  exact decode_encode s

/-- The transported `observe` yields the state: `decode_encode` cancels the
conjugation. -/
theorem slotObserve_self (s : Slot) : slotObserve () s = s := by
  unfold slotObserve
  exact decode_encode s

/-- The transported `replace` yields the replacement and reports `true`: the
description instance replaces unconditionally, and `decode_encode` cancels the
conjugation. -/
theorem slotReplace_self (new current : Slot) : slotReplace new current = (new, true) := by
  unfold slotReplace
  exact Prod.ext (decode_encode new) rfl

/-- The transported encoding is the description encoding after `encode`. -/
theorem slotEncodeRead_eq (s : Slot) :
    slotEncodeRead () s = encodeElSlotDesc (encode s) := rfl

/-! ## The transported instance

Every operation is the description instance's conjugated by `encode`/`decode`,
and every law is the corresponding description law after the conjugation is
cancelled with an inverse law: `initial_valid` and `replace_valid` use
`decode_encode` (through `slotInitial_self`/`slotReplace_self`),
`encodeRead_injective` uses it too (so injectivity of the description encoding
gives injectivity of the slot encoding), and `observe_detached` uses
`encode_decode` (so the description's no-reference law transfers back). -/

/-- The slot as a lawful state variable, transported from `slotDescStateVar`
across `encode` and `decode` rather than proved from nothing.

A state is a `Slot`, initialized from a `Slot`; the read operation is `Unit` and
returns the state, the write operation is the `Slot` to install, and a write
always takes effect (`true`). -/
instance slotStateVar : LawfulStateVar Slot Slot Unit Slot where
  Result _ := Slot
  initial := slotInitial
  Valid := slotValid
  observe := slotObserve
  replace := slotReplace
  encodeRead := slotEncodeRead
  initial_valid s := by
    show slotValid (slotInitial s)
    rw [slotInitial_self s]
    show slotDescStateVar.Valid (encode s)
    exact slotDescStateVar.initial_valid (encode s)
  replace_valid new current h := by
    show slotValid (slotReplace new current).1
    rw [slotReplace_self new current]
    show slotDescStateVar.Valid (encode new)
    exact slotDescStateVar.replace_valid (encode new) (encode current) h
  encodeRead_injective _ x y h := by
    have he : encode x = encode y :=
      slotDescStateVar.encodeRead_injective () (encode x) (encode y) h
    have hd := congrArg decode he
    rwa [decode_encode x, decode_encode y] at hd
  observe_detached ℓ _ s h := by
    show NoRef ℓ (slotDescStateVar.encodeRead ()
      (encode (decode (slotDescStateVar.observe () (encode s)))))
    rw [encode_decode]
    exact slotDescStateVar.observe_detached ℓ () (encode s) h

/-- The slot instance's `initial` is the slot itself: the description's `initial`
is the identity and `decode_encode` cancels the conjugation. -/
theorem slot_initial_eq (s : Slot) : LawfulStateVar.initial s = s :=
  slotInitial_self s

/-- Reading a slot yields the slot. -/
theorem slot_observe_eq (s : Slot) : LawfulStateVar.observe () s = s :=
  slotObserve_self s

/-- Replacing a slot with `new` yields `new` and reports `true`. -/
theorem slot_replace_eq (new current : Slot) :
    LawfulStateVar.replace new current = (new, true) :=
  slotReplace_self new current

/-! ## The slot's own facts -/

/-- Reading a slot after replacing it with `t` yields `t`: the transport of the
description instance's read-after-replace, through both inverse laws. -/
theorem slot_read_after_replace (s t : Slot) :
    LawfulStateVar.observe () (LawfulStateVar.replace t s).1 = t := by
  rw [slot_replace_eq t s]
  exact slot_observe_eq t

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
