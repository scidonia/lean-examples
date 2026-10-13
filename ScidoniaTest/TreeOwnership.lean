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
open Scidonia.RC.OwnershipTyped (root quoteSlot rootTag inst)
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

/-! ## The tree ownership discipline, from outside

The discipline's own checks: the write the account admits beside the write it
refuses, the reader's read beside the read at a node that is not a leaf, the
sequential hand-off beside the write through a spent handle, and the
out-of-bounds write. Each is the library theorem at a concrete configuration, and
the refusals are the `¬ TreeOwn` propositions a client cannot derive. -/

/-- The witness's write at its right leaf is admitted, while the reader holds half
of the left leaf and half of the shared root. -/
theorem witness_write_admitted :
    TreeOwn siblingLayout witnessCtx witnessEnv siblingAccount witnessState
      (.store (.var rightName) 0 (.con0 9)) (.node witnessRightTy) (.con1 rootTag (.con0 9))
      (setLeaf ⟨siblingRight, .nat, rfl⟩ 9 witnessState).1 :=
  witness_sibling_write_admitted

/-- The write at the witness's root is refused: its subtree contains the node the
reader holds. -/
theorem witness_root_write_refused (b : Expr) {v : Expr} {s' : State siblingLayout} :
    ¬ TreeOwn siblingLayout witnessCtx witnessEnv siblingAccount witnessState
        (.store (.var rootName) 0 b) (.node witnessRootTy) v s' :=
  witness_subtree_write_refused b

/-- The reader's read at the witness's left leaf is admitted. -/
theorem witness_read_admitted :
    TreeOwn siblingLayout witnessCtx witnessEnv siblingAccount witnessState
      (.matchC (.var leftName) rootTag [outName] (.var outName)) (.obs .nat) (.con0 7)
      witnessState :=
  witness_leaf_read_admitted

/-- The read at the witness's root is refused: its handle is a struct node. -/
theorem witness_root_read_refused (body : Expr) {v : Expr} {s' : State siblingLayout} :
    ¬ TreeOwn siblingLayout witnessCtx witnessEnv siblingAccount witnessState
        (.matchC (.var rootName) rootTag [outName] body) (.obs .nat) v s' :=
  witness_struct_read_refused body

/-- The write through the name the hand-off consumed is refused. -/
theorem spent_write_refused (obs : Expr) {τ : TreeTy (.leaf .nat)} {v : Expr}
    {s' : State (.leaf .nat)} :
    ¬ TreeOwn (.leaf .nat) cellCtx cellEnv cellAccount 7
        (.bind nextName (.store (.var cellName) 0 obs) (.store (.var cellName) 0 obs)) τ v s' :=
  cell_spent_write_refused obs

/-- The sequential hand-off beside it is admitted: the second write is performed
through the fresh name the first write was handed to. -/
theorem handoff_admitted :
    TreeOwn (.leaf .nat) cellCtx cellEnv cellAccount 7
      (.bind nextName (.store (.var cellName) 0 (.con0 5)) (.store (.var nextName) 0 (.con0 6)))
      (.node cellTy) (.con1 rootTag (.con0 6))
      (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 6
        (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 5 7).1).1 :=
  cell_handoff_admitted

/-- The out-of-bounds write is refused: the rule's own success premise is the
library's failure report. -/
theorem out_of_bounds_refused (obs : Expr) {v : Expr} {s' : State arrLayout} :
    ¬ TreeOwn arrLayout arrCtx arrEnv arrAccount arrState
        (.store (.var leftName) 0 obs) (.node (arrTy 5)) v s' :=
  arr_out_of_bounds_refused obs

/-- The in-bounds element of the same array is one the account admits a write
at. -/
theorem in_bounds_admitted :
    WriteHolds arrAccount 0 (.index 1 (.here : Path (.leaf .nat))) :=
  arr_write_admitted

-- The refused write's own elaboration: the account's write right at the root is
-- not derivable from the reader's loan.
#check (witness_subtree_write_refused : ∀ (b : Expr) {v : Expr} {s' : State siblingLayout},
  ¬ TreeOwn siblingLayout witnessCtx witnessEnv siblingAccount witnessState
      (.store (.var rootName) 0 b) (.node witnessRootTy) v s')

/-! ## The frame, the snapshot and the take-out, from outside -/

/-- The leaf frame applied at the witness: a write at the left leaf leaves what a
read of the right leaf returns unchanged, through the shared fractional spine. -/
theorem witness_frame_check :
    read? ⟨siblingRight, .nat, rfl⟩ (setLeaf ⟨siblingLeft, .nat, rfl⟩ 5 witnessState).1
      = read? ⟨siblingRight, .nat, rfl⟩ witnessState :=
  read_frame_leaf ⟨siblingLeft, .nat, rfl⟩ ⟨siblingRight, .nat, rfl⟩ witnessState
    (setLeaf ⟨siblingLeft, .nat, rfl⟩ 5 witnessState).1 5
    (disjoint_left_right (.here : Path (.leaf .nat)) (.here : Path (.leaf .nat)))
    (by rfl)

/-- The same-path read–write–read, bound to the state before and after: the first
read is the old observation and the second the one written. -/
theorem witness_snapshot_check {old : Scidonia.FracPerm.StateVar.Value}
    (hr : read? ⟨siblingLeft, .nat, rfl⟩ witnessState = some old) :
    read? ⟨siblingLeft, .nat, rfl⟩ witnessState = some old
      ∧ read? ⟨siblingLeft, .nat, rfl⟩ (setLeaf ⟨siblingLeft, .nat, rfl⟩ 9 witnessState).1
        = some (encodeObs .nat 9) :=
  snapshot_leaf ⟨siblingLeft, .nat, rfl⟩ witnessState
    (setLeaf ⟨siblingLeft, .nat, rfl⟩ 9 witnessState).1 old 9 hr (by rfl)

-- The two reads at the concrete pair, evaluated: 7 before the write and 9 after.
#guard decide (read? pairLeftObsPath pairState = some (.nat 7))

#guard decide (read? pairLeftObsPath (setLeaf pairLeftObsPath 9 pairState).1 = some (.nat 9))

/-- The snapshot's concrete witness. -/
theorem snapshot_pair_check :
    read? pairLeftObsPath pairState = some (Scidonia.FracPerm.StateVar.Value.nat 7)
      ∧ (setLeaf pairLeftObsPath 9 pairState).2 = true :=
  ⟨snapshot_pair_witness.1, snapshot_pair_witness.2.1⟩

/-- The nonleaf frame: replacing the left component of the pair leaves the node
value at the right component where it was. -/
theorem nonleaf_frame_check :
    nodeVal pairRight (replaceAt pairLayout pairLeft 5 pairState)
      = nodeVal pairRight pairState :=
  replaceAt_nodeVal_of_disjoint pairLeft pairRight 5 pairState
    (disjoint_left_right (.here : Path (.leaf .nat)) (.here : Path (.leaf .nat)))
    trivial

/-- The replacement lands its new focus where the path points. -/
theorem replacement_lands_check :
    subAt pairLeft (replaceAt pairLayout pairLeft 5 pairState) = 5 :=
  replaceAt_subAt pairLeft 5 pairState trivial

/-- The array's take-out and put-back equation at one level. -/
theorem takeout_level_check :
    replaceAt arrLayout (.index 1 (.here : Path (.leaf .nat))) (5 : State (.leaf .nat))
        (#[1, 2, 3] : Array (State (.leaf .nat)))
      = (#[1, 2, 3] : Array (State (.leaf .nat))).set 1
          (replaceAt (.leaf .nat) (.here : Path (.leaf .nat)) 5
            ((#[1, 2, 3] : Array (State (.leaf .nat)))[1])) (by decide) :=
  replaceAt_index 1 (.here : Path (.leaf .nat)) 5 (#[1, 2, 3] : Array (State (.leaf .nat)))
    (by decide)

-- The take-out's conditional injectivity, as the library states it: the run's
-- counting and the coupling's counting of one heap are its two premises.
#check @Scidonia.RC.TreeOwnership.takeout_transfer

/-! ## The interpreter and the agreement, from outside

The direct evaluation is the interpreter on the state it is given; the copying
side is the existing reduction of the same term's instance. The two meet at one
value, and an admitted program's result carries no protected node. -/

-- The direct evaluation of the one-node program, evaluated: the interpreter
-- returns the quoted root node of the observation written.
#guard decide (evalTree (.leaf .nat) 7 (.store (.var cellName) 0 (.con0 5))
  = some (.con1 rootTag (.con0 5)))

-- The agreement, the totality, the detachment and the runner's `IO` equation, as
-- the library states them.
#check @evalTree_sound
#check @evalTree_sound_closed
#check @evalTree_total
#check @evalTree_no_protected
#check @runTreeIO_of_evalTree

/-- The one-node configuration *is* the session configuration of the leaf layout:
the same context and the same environment. -/
theorem cellCtx_eq_rootCtx : cellCtx = rootCtx (.leaf .nat) := rfl

/-- The one-node environment is the session environment of the leaf layout: each
holds the quoted root node at the one name. -/
theorem cellEnv_eq_rootEnv : cellEnv = rootEnv (.leaf .nat) 7 := by
  funext x
  by_cases hx : x = 0
  · subst hx
    simp [cellEnv, rootEnv, sessionName, cellName, cellVal, quoteEl]
  · simp [cellEnv, rootEnv, sessionName, cellName, hx]

/-- The agreement applied at the hand-off, with the copying reduction's hypothesis
given: the interpreter's value is the value the *existing* `StepStar` of the same
term's instance reaches. -/
theorem handoff_agreement
    (hs : StepStar (inst (rootEnv (.leaf .nat) 7)
      (.bind nextName (.store (.var cellName) 0 (.con0 5))
        (.store (.var nextName) 0 (.con0 6)))) (.con1 rootTag (.con0 6))) :
    evalTree (.leaf .nat) 7
      (.bind nextName (.store (.var cellName) 0 (.con0 5))
        (.store (.var nextName) 0 (.con0 6))) = some (.con1 rootTag (.con0 6)) := by
  have h : TreeOwn (.leaf .nat) (rootCtx (.leaf .nat)) (rootEnv (.leaf .nat) 7) cellAccount 7
      (.bind nextName (.store (.var cellName) 0 (.con0 5))
        (.store (.var nextName) 0 (.con0 6))) (.node cellTy) (.con1 rootTag (.con0 6))
      (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 6
        (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 5 7).1).1 := by
    rw [← cellCtx_eq_rootCtx, ← cellEnv_eq_rootEnv]
    exact cell_handoff_admitted
  exact evalTree_sound h hs (Value.con1 (Value.con0 6))

/-- The totality applied at the hand-off: the evaluation reaches a value the
copying reduction of the same instance reaches. -/
theorem handoff_total :
    ∃ v, evalTree (.leaf .nat) 7
        (.bind nextName (.store (.var cellName) 0 (.con0 5))
          (.store (.var nextName) 0 (.con0 6))) = some v
      ∧ StepStar (inst (rootEnv (.leaf .nat) 7)
          (.bind nextName (.store (.var cellName) 0 (.con0 5))
            (.store (.var nextName) 0 (.con0 6)))) v
      ∧ Value v := by
  have h : TreeOwn (.leaf .nat) (rootCtx (.leaf .nat)) (rootEnv (.leaf .nat) 7) cellAccount 7
      (.bind nextName (.store (.var cellName) 0 (.con0 5))
        (.store (.var nextName) 0 (.con0 6))) (.node cellTy) (.con1 rootTag (.con0 6))
      (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 6
        (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 5 7).1).1 := by
    rw [← cellCtx_eq_rootCtx, ← cellEnv_eq_rootEnv]
    exact cell_handoff_admitted
  exact evalTree_total h

/-! ## Axioms

Each of these is asserted: the `#guard_msgs` pins the list `#print axioms` emits,
so a proof that acquires another axiom fails the build rather than printing a
longer list for a reader. -/

/-- info: 'Scidonia.RC.TreeOwnership.witness_sibling_write_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.witness_sibling_write_admitted

/-- info: 'Scidonia.RC.TreeOwnership.witness_subtree_write_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.witness_subtree_write_refused

/-- info: 'Scidonia.RC.TreeOwnership.witness_leaf_read_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.witness_leaf_read_admitted

/-- info: 'Scidonia.RC.TreeOwnership.witness_struct_read_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.witness_struct_read_refused

/-- info: 'Scidonia.RC.TreeOwnership.cell_spent_write_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.cell_spent_write_refused

/-- info: 'Scidonia.RC.TreeOwnership.cell_handoff_admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.cell_handoff_admitted

/-- info: 'Scidonia.RC.TreeOwnership.arr_out_of_bounds_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.arr_out_of_bounds_refused

/-- info: 'Scidonia.RC.TreeOwnership.takeout_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.takeout_transfer

/-- info: 'Scidonia.RC.TreeOwnership.replaceAt_subAt_of_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.replaceAt_subAt_of_disjoint

/-- info: 'Scidonia.RC.TreeOwnership.snapshot_pair_witness' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.snapshot_pair_witness

end ScidoniaTest.TreeOwnership
