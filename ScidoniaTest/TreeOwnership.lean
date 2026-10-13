/-
Checks for `Scidonia.RC.TreeOwnership` from outside the library.

The subject is a layout-indexed state, its quotation, its per-node fractional
account and the laws that account obeys. The checks here are of four kinds:

* **The quotation, evaluated**: the round trip at a struct of two naturals and at
  a nested array, the detector on a leaf's observation and on a leaf's node, and
  the alignment with the one-cell fragment's own slot quotation and root node.
* **Navigation, evaluated**: the path-resolution law at the paths of the struct
  and of the nested array, including an in-bounds array index, and the resolution
  of a path to an observation path.
* **The account, evaluated**: the sibling witness — a reader owning half of the
  common root and half of the left leaf, a writer owning the root's other half
  and the whole right subtree — read at the held fraction it computes.
* **Axioms**: each representative theorem's `#print axioms` output is pinned, so
  a proof that acquires an axiom fails the build rather than printing a longer
  list for a reader to notice.
-/
import Scidonia.RC

open Scidonia.RC
open Scidonia.RC.TreeOwnership
open Scidonia.RC.OwnershipTyped (root quoteSlot)
open Scidonia.FracPerm.StateVar (Slot encode decode halves_rejoin)
open Scidonia.FracPerm.StateVar.Layout5

namespace ScidoniaTest.TreeOwnership

/-! ## The quotation, evaluated -/

/-- The struct the quotation checks are read at: a pair of naturals. -/
abbrev pairLayout : Layout := .struct (.leaf .nat) (.leaf .nat)

/-- The struct's state. -/
abbrev pairState : State pairLayout := (7, 9)

/-- The nested array the quotation checks are read at. -/
abbrev nestedLayout : Layout := .arr (.arr (.leaf .nat))

/-- The nested array's state. -/
abbrev nestedState : State nestedLayout := #[#[1, 2], #[3, 4]]

/-
The quotation of a struct and of a nested array decodes back to the state it
quotes.
-/
#guard decide (unquoteVal pairLayout (cellVal pairLayout pairState) = some pairState)

#guard decide (unquoteVal nestedLayout (cellVal nestedLayout nestedState) = some nestedState)

/-- The quotation is injective at a nested array: two states with one quotation
are one state. -/
theorem nested_injective {s : State nestedLayout}
    (h : cellVal nestedLayout s = cellVal nestedLayout nestedState) : s = nestedState :=
  cellVal_injective h

/-
The detector: a leaf's observation carries no protected node, while a leaf's node
and a struct's node do.
-/
#guard decide (hasProtected (quoteEl .nat 5) = false)

#guard decide (hasProtected (cellVal (.leaf .nat) 5) = true)

#guard decide (hasProtected (cellVal pairLayout pairState) = true)

/-
The one-cell fragment's alignment: at the slot description a leaf's node value is
the fragment's root node and a leaf's observation is the fragment's slot
quotation.
-/
#guard decide (cellVal (.leaf (.sum .unit .nat)) (encode (Slot.full 7)) = root (Slot.full 7))

#guard decide (quoteEl (.sum .unit .nat) (encode (Slot.full 7)) = quoteSlot (Slot.full 7))

/-- The slot description's round trip, at every slot. -/
theorem slot_round_trip_all (s : Slot) :
    unquoteEl (.sum .unit .nat) (quoteEl (.sum .unit .nat) (encode s)) = some (encode s) :=
  unquoteEl_quoteEl (.sum .unit .nat) (encode s)

/-! ## Navigation, evaluated -/

/-- The left leaf's path in the struct. -/
abbrev pairLeft : Path pairLayout := .left (.here : Path (.leaf .nat))

/-- The right leaf's path in the struct. -/
abbrev pairRight : Path pairLayout := .right (.here : Path (.leaf .nat))

/-- The nested array's path to its second element's first element. -/
abbrev nestedPath : Path nestedLayout := .index 1 (.index 0 (.here : Path (.leaf .nat)))

/-
The path resolution, evaluated: navigating a state's quotation to a leaf of the
struct and to an in-bounds element of the nested array is the state's own node
there.
-/
#guard decide (nav pairLeft (cellVal pairLayout pairState) = some (nodeVal pairLeft pairState))

#guard decide (nav pairRight (cellVal pairLayout pairState) = some (nodeVal pairRight pairState))

#guard decide (nav nestedPath (cellVal nestedLayout nestedState) =
  some (nodeVal nestedPath nestedState))

/-- The path resolution, as a theorem at the nested array. -/
theorem nested_resolution :
    nav nestedPath (cellVal nestedLayout nestedState) = some (nodeVal nestedPath nestedState) := by
  have hb : InBounds nestedPath nestedState := ⟨#[3, 4], by decide, ⟨3, by decide, trivial⟩⟩
  exact nav_cellVal nestedLayout nestedState nestedPath hb

/-- The left path resolves to an observation path whose path is itself. -/
theorem pairLeft_resolves :
    (leafObsPath? pairLeft).map (fun q => q.path) = some pairLeft := rfl

/-- A path whose end is a struct addresses no leaf, so no read is admitted there:
the detector's negative result. -/
theorem pairRoot_not_leaf : (leafObsPath? (Path.here : Path pairLayout)).isNone = true := rfl

/-! ## The account, evaluated -/

/-
The sibling witness, evaluated: the root's two halves leave nothing held there,
the right leaf is held whole by its writer, and the left leaf's loan is the
account's.
-/
#guard decide (heldAt siblingAccount siblingRoot = 0)

#guard decide (heldAt siblingAccount siblingRight = 1)

/-- The witness's ledger at the left leaf is the reader's loan. -/
theorem sibling_left_ledger_at : ledgerAt siblingAccount siblingLeft = siblingLeftLedger :=
  sibling_ledger_left

/-- The witness's account is valid: at the same node the reader's half and the
writer's half fit in the whole. -/
theorem sibling_valid : ValidAccount siblingAccount := siblingAccount_valid

/-- The reader's share of the left leaf is positive, and the writer excludes
every reader of the right leaf: the exclusion is at the same node. -/
theorem sibling_reader_positive : 0 < (1 / 2 : Rat) := sibling_read_allowed.1

/-- The writer's admission of the right subtree is the account's. -/
theorem sibling_writer_owns : Writes siblingAccount siblingRight :=
  spine_sibling_compatible.2.2.1

/-- The two halves of the common root fill it exactly. -/
theorem sibling_halves : (1 / 2 : Rat) + 1 / 2 = 1 := halves_rejoin 1

/-! ## Axioms

Each of these is asserted: the `#guard_msgs` pins the list `#print axioms` emits,
so a proof that acquires another axiom fails the build rather than printing a
longer list. -/

/-- info: 'Scidonia.RC.TreeOwnership.unquoteEl_quoteEl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.unquoteEl_quoteEl

/-- info: 'Scidonia.RC.TreeOwnership.unquoteVal_cellVal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.unquoteVal_cellVal

/-- info: 'Scidonia.RC.TreeOwnership.cellVal_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.cellVal_injective

/-- info: 'Scidonia.RC.TreeOwnership.nav_cellVal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.nav_cellVal

/-- info: 'Scidonia.RC.TreeOwnership.quoteEl_hasProtected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.quoteEl_hasProtected

/-- info: 'Scidonia.RC.TreeOwnership.leafObsPath?_some' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.leafObsPath?_some

/-- info: 'Scidonia.RC.TreeOwnership.share_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.share_fit

/-- info: 'Scidonia.RC.TreeOwnership.spine_writer_excludes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.spine_writer_excludes

/-- info: 'Scidonia.RC.TreeOwnership.readThrough_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.readThrough_fits

end ScidoniaTest.TreeOwnership
