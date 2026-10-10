/-
Compile-time checks for the description universe's single lawful instance
(`Scidonia.FracPerm.StateVar.Universe`).

These live in the check library, so they see exactly what a client sees. The
controls are of four kinds, in the style of `ScidoniaTest/StateVar.lean`:

* The **encoding's** controls are runs: `encodeEl` at each shape the universe
  has — a unit, a natural, both summands of a sum, and all four summands of a
  nested sum — compared with the value they must produce.
* The **instance's** controls are the class's operations and the laws at
  descriptions of each shape, including the injectivity and no-reference laws
  quantified over *every* description.
* The **model's** controls are the generic M2 theorems applied at an arbitrary
  description: the read–write–read snapshot at `nat`, with the two observations
  bound to their cells, and the frame and validity lemmas beside it.
* The **transport's** controls are an independent isomorphism: `Bool` at
  `sum unit unit`, a description the slot does not use, so the transport is not
  exercised only by the one client it was written for.

The last section prints the axioms of representative theorems, so that an
inherited kernel principle can be told from a new assumption.
-/
import Scidonia.FracPerm

open Scidonia.FracPerm.StateVar

namespace ScidoniaTest.Universe

/-! ## Running the encoding

`check` fails the build when a run's value is not the expected one. -/

/-- Fail the elaboration unless `observed` is `expected`. -/
def check {α : Type} [BEq α] [Repr α] (name : String) (expected observed : α) : IO Unit := do
  unless expected == observed do
    throw (IO.userError s!"{name}: expected {repr expected}, observed {repr observed}")

/-- A nested description: a sum of a sum and a sum. It is the shape the
`#eval`s below need in order to exercise a tag beneath a tag. It is an `abbrev`
so that `El nestedDesc` is reducible for instance search and for the tactic
that reads the two elements below apart, exactly as `El` itself is. -/
abbrev nestedDesc : Desc := .sum (.sum .unit .nat) (.sum .nat .unit)

/- One case per constructor of `Desc`, and every summand of the nested
description. -/
#eval do
  check "unit" Value.unit (encodeEl Desc.unit ())
  check "nat" (Value.nat 7) (encodeEl Desc.nat 7)
  check "sum, left summand" (Value.inl (Value.nat 3))
    (encodeEl (.sum .nat .unit) (Sum.inl 3))
  check "sum, right summand" (Value.inr Value.unit)
    (encodeEl (.sum .nat .unit) (Sum.inr ()))
  check "nested sum, left and left" (Value.inl (Value.inl Value.unit))
    (encodeEl nestedDesc (Sum.inl (Sum.inl ())))
  check "nested sum, left and right" (Value.inl (Value.inr (Value.nat 7)))
    (encodeEl nestedDesc (Sum.inl (Sum.inr 7)))
  check "nested sum, right and left" (Value.inr (Value.inl (Value.nat 3)))
    (encodeEl nestedDesc (Sum.inr (Sum.inl 3)))
  check "nested sum, right and right" (Value.inr (Value.inr Value.unit))
    (encodeEl nestedDesc (Sum.inr (Sum.inr ())))

/-! ## The instance, at each shape

The class's operations, checked against their expected values. The expected
value's type fixes the operation's result type, so the class's indexed results
do not have to be named; a write names its instance because its operand type is
the write operation and the expected value does not determine it. -/

#eval do
  check "a unit read" (() : El Desc.unit)
    (LawfulStateVar.observe () (⟨()⟩ : Described Desc.unit))
  check "a natural read" (7 : El Desc.nat)
    (LawfulStateVar.observe () (⟨7⟩ : Described Desc.nat))
  check "a sum read" (Sum.inr 3 : El (Desc.sum Desc.unit Desc.nat))
    (LawfulStateVar.observe () (⟨Sum.inr 3⟩ : Described (Desc.sum Desc.unit Desc.nat)))
  check "a nested sum read" (Sum.inr (Sum.inl 3) : El nestedDesc)
    (LawfulStateVar.observe () (⟨Sum.inr (Sum.inl 3)⟩ : Described nestedDesc))
  check "a nested sum write reports true" (true : Bool)
    ((describedStateVar nestedDesc).replace (Sum.inr (Sum.inl 3))
      (⟨Sum.inl (Sum.inl ())⟩ : Described nestedDesc)).2

/-- Reading after replacing yields the replacement, at the unit description. -/
example : (describedStateVar Desc.unit).observe ()
    ((describedStateVar Desc.unit).replace () (⟨()⟩ : Described Desc.unit)).1 = () :=
  universe_read_after_replace Desc.unit ⟨()⟩ ()

/-- Reading after replacing yields the replacement, at a nested sum. -/
example : (describedStateVar nestedDesc).observe ()
    ((describedStateVar nestedDesc).replace (Sum.inr (Sum.inl 3))
      (⟨Sum.inl (Sum.inl ())⟩ : Described nestedDesc)).1 = Sum.inr (Sum.inl 3) :=
  universe_read_after_replace nestedDesc ⟨Sum.inl (Sum.inl ())⟩ (Sum.inr (Sum.inl 3))

/-- Reading after replacing yields the replacement, at an arbitrary
description. -/
example (d : Desc) (s : Described d) (x : El d) :
    (describedStateVar d).observe () ((describedStateVar d).replace x s).1 = x :=
  universe_read_after_replace d s x

/-- The encoded observation of *every* description is detached from every
root. -/
example (d : Desc) (ℓ : Loc) (s : Described d) :
    NoRef ℓ (encodeEl d ((describedStateVar d).observe () s)) :=
  universe_read_detached d ℓ s

/-- The instance's injectivity field is the universe's injectivity lemma and not
a per-description proof. -/
example (d : Desc) (x y : El d) :
    (describedStateVar d).encodeRead_injective () x y = encodeEl_injective d x y := rfl

/-! ## The encoding is injective, and its detector is not vacuous

Injectivity at every description, quantified as a client sees it, and its use:
distinct elements of a nested description encode distinctly. -/

/-- Injectivity at every description. -/
example : ∀ (d : Desc) (x y : El d), encodeEl d x = encodeEl d y → x = y :=
  encodeEl_injective

/-- Distinct elements of a nested description encode distinctly. -/
example : encodeEl nestedDesc (Sum.inl (Sum.inl ())) ≠
    encodeEl nestedDesc (Sum.inl (Sum.inr 7)) := by
  intro h
  exact absurd (encodeEl_injective nestedDesc _ _ h) (by decide)

/-- The encoding of each shape is detached from root 0. -/
example : NoRef 0 (encodeEl Desc.unit ()) := trivial

example : NoRef 0 (encodeEl Desc.nat 5) := trivial

example : NoRef 0 (encodeEl (Desc.sum Desc.unit Desc.nat) (Sum.inr 5)) := trivial

example : NoRef 0 (encodeEl nestedDesc (Sum.inl (Sum.inr 5))) := trivial

/-- The detector's own negative control: the location at root 0 is *not*
detached from root 0, so the passing `NoRef`s above are not vacuous. -/
example : ¬ NoRef 0 (Value.loc 0) := not_noRef_loc_self 0

/-! ## The generic model at an arbitrary description

A client-side heap over the natural description: root 0 holds a wrapper of `7`.
The theorems below are the generic M2 ones, applied at `describedStateVar`
rather than re-proved. -/

/-- The heap before the demo write: root 0 holds a wrapper of `7`. -/
def natHeap : Heap (Described Desc.nat) :=
  fun ℓ => if ℓ = 0 then some ⟨7⟩ else none

/-- The heap after the demo write of `9` at root 0. -/
def natHeap' : Heap (Described Desc.nat) :=
  Heap.update natHeap 0 (some ⟨9⟩)

/-- The pre-write read observes `7`. -/
example : ReadAt (describedStateVar Desc.nat) 0 () natHeap natHeap (7 : El Desc.nat) :=
  ⟨⟨7⟩, by simp [At, natHeap], trivial, rfl, rfl⟩

/-- The write installs `9` at root 0 and reports that it took effect. -/
example : WriteAt (describedStateVar Desc.nat) 0 (9 : El Desc.nat) natHeap natHeap' true :=
  ⟨⟨7⟩, by simp [At, natHeap], trivial, rfl, rfl⟩

/-- The post-write cell holds a wrapper of `9`. -/
example : At 0 (⟨9⟩ : Described Desc.nat) natHeap' := by
  show natHeap' 0 = some (⟨9⟩ : Described Desc.nat)
  rw [natHeap', Heap.update_self]

/-- The snapshot at an arbitrary description: the pre-write observation `7` is
bound to the pre-write cell and the post-write observation `9` to the post-write
cell. -/
example : ∃ s : Described Desc.nat, At 0 s natHeap ∧
    (7 : El Desc.nat) = (describedStateVar Desc.nat).observe () s ∧
    (9 : El Desc.nat) =
      (describedStateVar Desc.nat).observe () ((describedStateVar Desc.nat).replace 9 s).1 :=
  universe_snapshot_after_write Desc.nat
    (⟨⟨7⟩, by simp [At, natHeap], trivial, rfl, rfl⟩ :
      ReadAt (describedStateVar Desc.nat) 0 () natHeap natHeap (7 : El Desc.nat))
    (⟨⟨7⟩, by simp [At, natHeap], trivial, rfl, rfl⟩ :
      WriteAt (describedStateVar Desc.nat) 0 (9 : El Desc.nat) natHeap natHeap' true)
    (⟨⟨9⟩, by
        show natHeap' 0 = some (⟨9⟩ : Described Desc.nat)
        rw [natHeap', Heap.update_self], trivial, rfl, rfl⟩ :
      ReadAt (describedStateVar Desc.nat) 0 () natHeap' natHeap' (9 : El Desc.nat))

/-- A write at an arbitrary description leaves an admissible state in the
cell. -/
example : ∃ s' : Described Desc.nat, At 0 s' natHeap' ∧
    (describedStateVar Desc.nat).Valid s' :=
  universe_write_at_valid Desc.nat
    (⟨⟨7⟩, by simp [At, natHeap], trivial, rfl, rfl⟩ :
      WriteAt (describedStateVar Desc.nat) 0 (9 : El Desc.nat) natHeap natHeap' true)

/-- A write at an arbitrary description changes no cell other than its root. -/
example : natHeap' 4 = natHeap 4 :=
  universe_write_at_frame Desc.nat
    (⟨⟨7⟩, by simp [At, natHeap], trivial, rfl, rfl⟩ :
      WriteAt (describedStateVar Desc.nat) 0 (9 : El Desc.nat) natHeap natHeap' true)
    (by decide)

/-! ## The transport, at an isomorphism the slot does not use

`Bool` is isomorphic to `El (sum unit unit)`, so `transport` gives it a lawful
instance without any new proof: the instance's laws are the universe's, with the
isomorphism's inverse laws cancelling the conjugation. -/

/-- A description of two units, whose element type is isomorphic to `Bool`. -/
def boolDesc : Desc := .sum .unit .unit

/-- The isomorphism's forward map: `true` is the left unit, `false` the
right. -/
def boolToEl : Bool → El boolDesc
  | true => Sum.inl ()
  | false => Sum.inr ()

/-- The isomorphism's backward map. -/
def elToBool : El boolDesc → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

/-- One inverse law of the `Bool` isomorphism. -/
theorem elToBool_boolToEl (b : Bool) : elToBool (boolToEl b) = b := by
  cases b <;> rfl

/-- The other inverse law of the `Bool` isomorphism. -/
theorem boolToEl_elToBool (x : El boolDesc) : boolToEl (elToBool x) = x := by
  obtain (u | u) := x <;> cases u <;> rfl

/-- `Bool`, obtained from `transport` at a description the slot does not use. -/
instance boolStateVar : LawfulStateVar Bool Bool Unit Bool :=
  transport boolDesc Bool boolToEl elToBool elToBool_boolToEl boolToEl_elToBool

/-- The transported read returns the state, and the transported write installs
its operand: `transport`'s operations, computed. -/
example : LawfulStateVar.observe () true = true := rfl

example : LawfulStateVar.replace false true = (false, true) := rfl

/-- Reading after replacing at `Bool`, which uses both inverse laws. -/
example : LawfulStateVar.observe () (LawfulStateVar.replace false true).1 = false :=
  transport_read_after_replace boolDesc Bool boolToEl elToBool elToBool_boolToEl
    boolToEl_elToBool true false

/-- The transported encoding is `encodeEl` of the element the state names. -/
example : (boolStateVar : LawfulStateVar Bool Bool Unit Bool).encodeRead () true =
    encodeEl boolDesc (Sum.inl ()) := rfl

/-! ## Axioms of representative theorems

Only the standard kernel principles — `propext`, `Classical.choice`,
`Quot.sound` — may appear; a name of this development appearing here would be a
new assumption. -/

#print axioms Scidonia.FracPerm.StateVar.encodeEl_injective
#print axioms Scidonia.FracPerm.StateVar.encodeEl_noRef
#print axioms Scidonia.FracPerm.StateVar.describedStateVar
#print axioms Scidonia.FracPerm.StateVar.universe_read_after_replace
#print axioms Scidonia.FracPerm.StateVar.universe_read_detached
#print axioms Scidonia.FracPerm.StateVar.universe_read_at_detached
#print axioms Scidonia.FracPerm.StateVar.universe_write_at_valid
#print axioms Scidonia.FracPerm.StateVar.universe_write_at_frame
#print axioms Scidonia.FracPerm.StateVar.universe_snapshot_after_write
#print axioms Scidonia.FracPerm.StateVar.transport
#print axioms Scidonia.FracPerm.StateVar.transport_read_after_replace

end ScidoniaTest.Universe
