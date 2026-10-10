/-
The logical value language of the generic state-variable interface, and the
no-reference predicate over it.

`Value` is an *observation encoding*: the closed type in which a lawful state
variable's primitive reads describe their results when the model has to say what
a read may hand back. It is deliberately small — a location, a unit, a natural,
an unsigned machine word, a boolean, an option, a sum and a pair — so that a
class law can quantify over every shape a modeled read result may take without
the encoding being open.

`loc address` is the one constructor that names a protected root. A `nat` or
`uint` payload is immutable data that a read may share freely; a `loc n` is a
reference to a root cell, and the state-variable class's no-reference
obligation forbids one in a primitive observation. The difference is in the
constructor tags, which is why the language has both a `.nat` case and a `.loc`
case rather than a single numeric one.

What this buys, and what it does not: `NoRef ℓ v` is a proposition about the
encoding, and `LawfulStateVar.observe_detached` refuses a modeled `.loc ℓ`
under a primitive observation of a valid state. It is **not** a theorem about
Lean's object graph, reference counting or foreign pointers; an encoding that
declined to represent a real run-time pointer as `.loc` would not be caught by
it. The in-place evidence for the array interface is the run-time harness
(`ScidoniaInPlace`), and the class is not advertised as certifying Lean's
physical no-alias property.

This module imports core and `Std` only, and it adds no runtime code: `Value`
appears in the model's observation encoding, never on a client-facing runtime
path.
-/
namespace Scidonia.FracPerm.StateVar

/-- A logical location: the address of a single root cell in the model's
single-root heap (`Scidonia.FracPerm.StateVar.Heap`). -/
abbrev Loc := Nat

/-- The logical value language a primitive read's result is encoded in.

`loc address` names a root cell; every other constructor is immutable data. The
sum, option and pair cases exist so that a class law can reach a location
*beneath* a compound observation — an obligation that only looked at the top
constructor would not.

This is a logical encoding, not Lean's object graph; see the module note. -/
inductive Value where
  /-- A reference to the root cell at `address`. -/
  | loc (address : Loc)
  /-- The unit value. -/
  | unit
  /-- A natural number. -/
  | nat (n : Nat)
  /-- An unsigned machine word. -/
  | uint (n : UInt64)
  /-- A boolean. -/
  | bool (b : Bool)
  /-- Nothing. -/
  | none
  /-- Something. -/
  | some (v : Value)
  /-- The left summand. -/
  | inl (v : Value)
  /-- The right summand. -/
  | inr (v : Value)
  /-- A pair. -/
  | pair (l r : Value)
deriving Repr, DecidableEq

/-- `NoRef ℓ v` says `v` names no root at `ℓ`.

A `.loc k` is detached from `ℓ` exactly when `k ≠ ℓ`; the predicate descends
through `some`, `inl`, `inr` and `pair`, so a location hidden beneath a
compound observation is still caught; every other constructor is immutable data
and is detached from every `ℓ`. -/
def NoRef (ℓ : Loc) : Value → Prop
  | .loc k    => k ≠ ℓ
  | .some v   => NoRef ℓ v
  | .inl v    => NoRef ℓ v
  | .inr v    => NoRef ℓ v
  | .pair x y => NoRef ℓ x ∧ NoRef ℓ y
  | _         => True

/-- A location is detached from `ℓ` exactly when it does not name `ℓ`. -/
theorem noRef_loc {ℓ k : Loc} : NoRef ℓ (.loc k) ↔ k ≠ ℓ := Iff.rfl

/-- Detachment descends through `some`. -/
theorem noRef_some {ℓ : Loc} {v : Value} : NoRef ℓ (.some v) ↔ NoRef ℓ v := Iff.rfl

/-- Detachment descends through `inl`. -/
theorem noRef_inl {ℓ : Loc} {v : Value} : NoRef ℓ (.inl v) ↔ NoRef ℓ v := Iff.rfl

/-- Detachment descends through `inr`. -/
theorem noRef_inr {ℓ : Loc} {v : Value} : NoRef ℓ (.inr v) ↔ NoRef ℓ v := Iff.rfl

/-- Detachment of a pair is detachment of both components. -/
theorem noRef_pair {ℓ : Loc} {x y : Value} :
    NoRef ℓ (.pair x y) ↔ NoRef ℓ x ∧ NoRef ℓ y := Iff.rfl

/-- A natural number is detached from every root. -/
theorem noRef_nat (ℓ : Loc) (n : Nat) : NoRef ℓ (.nat n) := trivial

/-- A machine word is detached from every root. -/
theorem noRef_uint (ℓ : Loc) (n : UInt64) : NoRef ℓ (.uint n) := trivial

/-- The unit value is detached from every root. -/
theorem noRef_unit (ℓ : Loc) : NoRef ℓ (.unit : Value) := trivial

/-- A location at a *different* root is detached. -/
theorem noRef_loc_of_ne {ℓ k : Loc} (h : k ≠ ℓ) : NoRef ℓ (.loc k) := h

/-- A location at `ℓ` itself is a reference to the protected root, so it is not
detached. This is the fact the class's countermodels turn on. -/
theorem not_noRef_loc_self (ℓ : Loc) : ¬ NoRef ℓ (.loc ℓ) := fun h => h rfl

end Scidonia.FracPerm.StateVar
