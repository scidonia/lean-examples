/-
Descriptions of a small universe of structured types, and the type each
description denotes.

`Desc` is a type *description*: a unit, a natural, or a sum of two descriptions.
`El d` is the Lean type the description `d` denotes, and `slotDesc` is the
description of a slot: a unit summed with a natural.

This is the syntax a description-indexed state variable is written against. The
description of the worked slot (`Scidonia.FracPerm.StateVar.Slot`) is
`slotDesc`, whose `El` is `Sum Unit Nat`, so a slot's encoding is a case of a
unit summand and a natural summand. The description is deliberately
non-recursive: `El d` is built from `Unit`, `Nat` and `Sum` alone, so a proof
over it is a finite case analysis rather than a fixpoint.

The module is only the universe: it defines no state variable and no proof. The
worked slot's witness and the theorems that use it live in
`Scidonia.FracPerm.StateVar.Slot`.
-/
namespace Scidonia.FracPerm.StateVar

/-- A description of a type in the small structural universe: a unit, a natural,
or a sum of two descriptions. -/
inductive Desc where
  /-- The unit type. -/
  | unit
  /-- The type of naturals. -/
  | nat
  /-- The sum of two described types. -/
  | sum (left right : Desc)
deriving DecidableEq, Repr

/-- The type a description denotes: `Unit`, `Nat`, or a `Sum` of the two
sub-descriptions' types.

`El` is an `abbrev`, so `El slotDesc` is reducible for a client: `Sum Unit Nat`
is its definitional form, and a literal such as `Sum.inr 7` can be given at an
`El` type without a type ascription. -/
abbrev El : Desc → Type
  | .unit => Unit
  | .nat => Nat
  | .sum left right => Sum (El left) (El right)

/-- The description of a slot: a unit (the empty slot) summed with a natural
(the payload of a full slot). -/
def slotDesc : Desc := .sum .unit .nat

end Scidonia.FracPerm.StateVar
