/-
Checks for `Scidonia.RC.TreeOwnership` from outside the library.

The subject is a layout-indexed state, its quotation, its per-node fractional
account, the laws that account obeys and the ownership discipline read at
concrete configurations. The checks here are of six kinds:

* **The quotation, evaluated**: the round trip at a struct of two naturals and at
  a nested array, the detector on a leaf's observation and on a leaf's node, and
  the alignment with the one-cell fragment's own slot quotation and root node.
* **Navigation, evaluated**: the path-resolution law at the paths of the struct
  and of the nested array, including an in-bounds array index, and the resolution
  of a path to an observation path.
* **The account, evaluated**: the sibling witness — a reader owning half of the
  common root and half of the left leaf, a writer owning the root's other half
  and the whole right subtree — and the three-holder witness, both read at the
  held fraction they compute.
* **The discipline at the boundary.** Each affirmative control is *evaluated*: the
  session program that performs it is run by the real `evalTree`, its result is
  pinned by a `#guard`, and the library's simulation against the existing
  `RC.StepStar` is applied to the admitted derivation. Each refusal is the
  library's `¬ TreeOwn` proposition at a concrete configuration.
* **The executable's surface.** The evaluation's signature is pinned and an
  account in the state's position is refused, so the guarantee that no authority
  representation reaches the executable is checked at the boundary rather than
  stated alone.
* **Axioms**: each representative theorem's `#print axioms` output is pinned, so
  a proof that acquires an axiom fails the build rather than printing a longer
  list for a reader to notice.
-/
import Scidonia.RC

open Scidonia.RC
open Scidonia.RC.TreeOwnership
open Scidonia.RC.OwnershipTyped (root quoteSlot rootTag inst Obs Fragment VEnv)
open Scidonia.FracPerm.StateVar (Slot encode decode halves_rejoin ValidShare)
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

/-
The three-holder witness, evaluated: one node whose holders hold a half, a
quarter and a quarter, the node filled by the three of them, and the conservation
of the node's own fraction step by step.
-/
#guard decide (heldAt halfAccount nodePath = 1 / 2)

#guard decide (heldAt forkAccount nodePath = 1 / 2)

#guard decide (heldAt multiAccount nodePath = 0)

/-- The three-holder account is valid: its holders fit in the node. -/
theorem multi_valid : ValidAccount multiAccount := multiAccount_valid

/-- The three-holder account's loans: a half, a quarter and a quarter. -/
theorem multi_holders : Reads multiAccount nodePath 0 (1 / 4)
    ∧ Reads multiAccount nodePath 1 (1 / 4) ∧ Reads multiAccount nodePath 2 (1 / 2) :=
  multi_reads

/-- The three-holder account's conservation: the two loans move the node's own
fraction by exactly their fractions, and the fork leaves it where it was. -/
theorem multi_conserved :
    heldAt halfAccount nodePath = heldAt nodeAccount nodePath - 1 / 2
      ∧ heldAt forkAccount nodePath = heldAt halfAccount nodePath
      ∧ heldAt multiAccount nodePath = heldAt forkAccount nodePath - 1 / 2 :=
  multi_conservation

/-- A fork's half is a valid share: the split the account makes is the halving of
the share it splits. -/
theorem fork_halves_valid : ValidShare (1 / 4) := by
  rw [quarter_eq]
  exact half_share_valid one_half_valid

/-- A loan bigger than what the node's owner still holds would overfill it: the
conservation premise the account's own lending law carries. -/
theorem lend_fits_refused : ¬ ((1 : Rat) / 2 + 1 / 2 + 1 / 2 ≤ 1) := by grind

/-! ## The tree ownership discipline, from outside

The discipline's own checks: the write the account admits beside the write it
refuses, the reader's read beside the read at a node that is not a leaf, the
sequential hand-off beside the write through a spent handle and beside the write
handed two names of one subtree, and the nonleaf replacement's two controls.
-/

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

/-- The write handed *two* names of one subtree is refused: the context that would
carry it holds the one node at two names. -/
theorem two_name_refused (obs obs' : Expr) {τ : TreeTy (.leaf .nat)} {v : Expr}
    {s' : State (.leaf .nat)} :
    ¬ TreeOwn (.leaf .nat) aliasCtx cellEnv cellAccount 7
        (.bind nextName (.store (.var cellName) 0 obs) (.store (.var aliasName) 0 obs')) τ v s' :=
  cell_two_name_refused obs obs'

/-- The same shape with one name is admitted: the refusal is the two names. -/
theorem two_name_control :
    TreeOwn (.leaf .nat) cellCtx cellEnv cellAccount 7
      (.bind nextName (.store (.var cellName) 0 (.con0 5)) (.store (.var nextName) 0 (.con0 6)))
      (.node cellTy) (.con1 rootTag (.con0 6))
      (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 6
        (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 5 7).1).1 :=
  cell_two_name_control

/-- An admitted derivation's name is the path's only live one: the second name
that would carry a second write of the same subtree does not exist. -/
theorem handle_unique {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv} {A : Account d}
    {s : State d} {e : Expr} {τ : TreeTy d} {v : Expr} {s' : State d}
    (h : TreeOwn d Γ ρ A s e τ v s') :
    ∀ x y n m, Γ x = some (.node n) → Γ y = some (.node m) → n.path = m.path → x = y :=
  treeOwn_handleWF h

/-- Every admitted derivation's account is valid: the per-node conservation
discipline is an index of the rules. -/
theorem admitted_account_valid {τ : TreeTy (.leaf .nat)} {v : Expr} {s' : State (.leaf .nat)} :
    ValidAccount cellAccount :=
  treeOwn_validAccount cell_handoff_admitted (τ := (.node cellTy)) (v := .con1 rootTag (.con0 6))
    (s' := _)

/-- The nonleaf replacement at an index the state does not have is refused: the
replacement answers `none` there. -/
theorem nonleaf_out_of_bounds_refused (b : Expr) {v : Expr} {s' : State subLayout} :
    ¬ TreeOwn subLayout subCtx subEnv subAccount subState
        (.store (.var leftName) 0 b) (.node subMissingTy) v s' :=
  sub_out_of_bounds_refused b

/-- The in-bounds nonleaf control of the same shape is admitted. -/
theorem nonleaf_in_bounds_admitted :
    ∃ s' : State subLayout,
      TreeOwn subLayout subCtx subEnv subAccount subState
        (.store (.var rootName) 0 (.con1 rootTag (.con0 5))) (.node subTy)
        (.con2 structTag (.con1 rootTag (.con0 5)) (.con1 rootTag (.con0 2))) s' :=
  sub_in_bounds_admitted

/-- The bounds the rule's own success premise carries: a replacement that answers
`some` is at an in-bounds path, so the nonleaf rule's success is the state's
bounds and not a state the replacement did not touch. -/
theorem replacement_bounds {d : Layout} (p : Path d) (y : State (At p)) (s : State d)
    {s' : State d} (h : replaceAt d p y s = some s') : InBounds p s :=
  replaceAt_inBounds p y s h

-- The refused write's own elaboration: the account's write right at the root is
-- not derivable from the reader's loan.
#check (witness_subtree_write_refused : ∀ (b : Expr) {v : Expr} {s' : State siblingLayout},
  ¬ TreeOwn siblingLayout witnessCtx witnessEnv siblingAccount witnessState
      (.store (.var rootName) 0 b) (.node witnessRootTy) v s')

/-! ## The discipline at the session boundary, evaluated

Each affirmative control below is read at the *session* configuration the runner
begins from — the one name the state's root is held under — and each is evaluated:
the program is run by the real `evalTree`, its result is pinned by a `#guard`, and
the library's simulation gives the existing `RC.StepStar` of the program's instance
at that same value.
-/

/-- The name a struct descent binds to a node's left component. -/
def midName : Var := 30

/-- The name a struct descent binds to a node's right component. -/
def tailName : Var := 31

/-- The left component's path from the session's root. -/
def sessionLeft : Path siblingLayout := leftPath (Path.here : Path siblingLayout) rfl

/-- The right component's path from the session's root. -/
def sessionRight : Path siblingLayout := rightPath (Path.here : Path siblingLayout) rfl

/-- The handle the session's descent installs for the left component. -/
def sessionLeftTy : NodeTy siblingLayout :=
  .at 0 sessionLeft (.leaf .nat) (leftPath_at (Path.here : Path siblingLayout) rfl)

/-- The handle the session's descent installs for the right component. -/
def sessionRightTy : NodeTy siblingLayout :=
  .at 0 sessionRight (.leaf .nat) (rightPath_at (Path.here : Path siblingLayout) rfl)

/-- The session's context after the descent's first binding. -/
def sessionCtxL : Var → Option (TreeTy siblingLayout) :=
  extendTy (rootCtx siblingLayout) midName (.node sessionLeftTy)

/-- The session's context after the descent: both components bound under the
root's holder. -/
def sessionCtx : Var → Option (TreeTy siblingLayout) :=
  extendTy sessionCtxL tailName (.node sessionRightTy)

/-- The session's first binding holds one live handle per path. -/
theorem sessionCtxL_handleWF : HandleWF sessionCtxL :=
  (rootCtx_handleWF siblingLayout).extendTy_node (by
    intro z m hz
    have hm := rootCtx_bindsPaths siblingLayout z m hz
    simp at hm
    rw [hm]
    decide)

/-- The paths the session's first binding can bind. -/
theorem sessionCtxL_bindsPaths : BindsPaths sessionCtxL [sessionLeft, Path.here] :=
  (rootCtx_bindsPaths siblingLayout).extendTy_node

/-- The session's context holds one live handle per path. -/
theorem sessionCtx_handleWF : HandleWF sessionCtx :=
  sessionCtxL_handleWF.extendTy_node (by
    intro z m hz
    have hm := sessionCtxL_bindsPaths z m hz
    simp at hm
    rcases hm with hm | hm
    · rw [hm]; decide
    · rw [hm]; decide)

/-- The session's context binds its left component's name to the left component's
node. -/
theorem sessionCtx_mid : sessionCtx midName = some (.node sessionLeftTy) := by
  simp [sessionCtx, sessionCtxL, extendTy, midName, tailName]

/-- The session's context binds its right component's name to the right
component's node. -/
theorem sessionCtx_tail : sessionCtx tailName = some (.node sessionRightTy) := by
  simp [sessionCtx, sessionCtxL, extendTy, midName, tailName]

/-- The session's context holds nothing at a name the descent did not bind. -/
theorem sessionCtx_out : sessionCtx outName = none := by
  simp [sessionCtx, sessionCtxL, rootCtx, extendTy, midName, tailName, outName, sessionName]

/-- The session program that writes the witness's right leaf under the shared
root: a descent into the struct, then the write through the component's name. -/
def siblingProgram : Expr :=
  .matchC (.var sessionName) structTag [midName, tailName] (.store (.var tailName) 0 (.con0 5))

/-- The session program that reads the witness's left leaf under the shared root:
a descent into the struct, then the read through the component's name. -/
def readProgram : Expr :=
  .matchC (.var sessionName) structTag [midName, tailName]
    (.matchC (.var midName) rootTag [outName] (.var outName))

/-- The session's write of the right leaf under the shared root is admitted: the
descent installs the component's handle under the root's holder, and the account's
write right at the right leaf is read at the same node. -/
theorem session_write_admitted :
    TreeOwn siblingLayout (rootCtx siblingLayout) (rootEnv siblingLayout witnessState)
      siblingAccount witnessState siblingProgram (.node sessionRightTy) (.con1 rootTag (.con0 5))
      (setLeaf ⟨siblingRight, .nat, rfl⟩ 5 witnessState).1 := by
  refine TreeOwn.descendStruct (x := sessionName) (y := midName) (z := tailName)
    (body := .store (.var tailName) 0 (.con0 5)) (w := 0)
    (p := (Path.here : Path siblingLayout)) (a := .leaf .nat) (c := .leaf .nat) (h := rfl)
    (v₁ := .con1 rootTag (.con0 7)) (v₂ := .con1 rootTag (.con0 9)) (τ := (.node sessionRightTy))
    (v' := .con1 rootTag (.con0 5)) (s' := (setLeaf ⟨siblingRight, .nat, rfl⟩ 5 witnessState).1)
    (hA := siblingAccount_valid) (hΓ := rootCtx_handleWF siblingLayout)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [rootCtx, rootNode, siblingLayout, sessionName]
  · simp only [rootEnv, sessionName, reduceIte]
    rw [cellVal_struct, cellVal_leaf, cellVal_leaf, quoteEl]
    rfl
  · simp [rootCtx, sessionName, midName, tailName]
  · simp [rootEnv, sessionName, midName, tailName]
  · simp [rootCtx, sessionName, midName, tailName]
  · simp [rootEnv, sessionName, midName, tailName]
  · decide
  · refine TreeOwn.write (x := tailName) (a := .con0 5) (w := 0) (p := sessionRight)
      (o := .nat) (h := rfl) (v := .con0 9) (xel := 5)
      (s' := (setLeaf ⟨siblingRight, .nat, rfl⟩ 5 witnessState).1)
      (hA := siblingAccount_valid) (hΓ := sessionCtx_handleWF) ?_ ?_ ?_ ?_ ?_ ?_
    · exact sessionCtx_tail
    · rw [VEnv.extend_self]
    · exact Obs.nat 5
    · rfl
    · exact witness_right_writeHolds_root
    · rfl

/-
The session's write of the right leaf, evaluated: the real interpreter returns the
observation written.
-/
#guard decide (evalTree siblingLayout witnessState siblingProgram = some (.con1 rootTag (.con0 5)))

/-- The session's write, with the copying side given: the real `evalTree`'s value is
the value the *existing* `StepStar` of the program's instance reaches. -/
theorem session_write_agrees
    (hs : StepStar (inst (rootEnv siblingLayout witnessState) siblingProgram)
      (.con1 rootTag (.con0 5))) :
    evalTree siblingLayout witnessState siblingProgram = some (.con1 rootTag (.con0 5)) :=
  evalTree_sound session_write_admitted hs (Value.con1 (Value.con0 5))

/-- The session's write reaches a value the same reduction reaches: the simulation's
totality applied to the admitted derivation. -/
theorem session_write_total :
    ∃ v, evalTree siblingLayout witnessState siblingProgram = some v
      ∧ StepStar (inst (rootEnv siblingLayout witnessState) siblingProgram) v ∧ Value v :=
  evalTree_total session_write_admitted

/-- The session's read of the left leaf is admitted under the reader's own loan:
the descent installs the component's handle, and the read's borrow is the reader's
half of the shared root and of the leaf. -/
theorem session_read_admitted :
    TreeOwn siblingLayout (rootCtx siblingLayout) (rootEnv siblingLayout witnessState)
      siblingAccount witnessState readProgram (.obs .nat) (.con0 7) witnessState :=
  TreeOwn.descendStruct (x := sessionName) (y := midName) (z := tailName)
    (body := .matchC (.var midName) rootTag [outName] (.var outName)) (w := 0)
    (p := (Path.here : Path siblingLayout)) (a := .leaf .nat) (c := .leaf .nat) (h := rfl)
    (v₁ := .con1 rootTag (.con0 7)) (v₂ := .con1 rootTag (.con0 9)) (τ := (.obs .nat))
    (v' := .con0 7) (s' := witnessState)
    (hA := siblingAccount_valid) (hΓ := rootCtx_handleWF siblingLayout)
    (by simp [rootCtx, rootNode, siblingLayout, sessionName])
    (by
      simp only [rootEnv, sessionName, reduceIte]
      rw [cellVal_struct, cellVal_leaf, cellVal_leaf, quoteEl]
      rfl)
    (by simp [rootCtx, sessionName, midName, tailName])
    (by simp [rootEnv, sessionName, midName, tailName])
    (by simp [rootCtx, sessionName, midName, tailName])
    (by simp [rootEnv, sessionName, midName, tailName])
    (by decide)
    (TreeOwn.read (x := midName) (y := outName) (body := .var outName) (w := 0) (p := sessionLeft)
      (o := .nat) (h := rfl) (share := fun _ => 1 / 2) (v := .con0 7) (xel := 7)
      (τ := (.obs .nat)) (v' := .con0 7) (s' := witnessState)
      (hA := siblingAccount_valid) (hΓ := sessionCtx_handleWF) sessionCtx_mid
      (by rw [VEnv.extend_of_ne (by decide : midName ≠ tailName), VEnv.extend_self])
      rfl witnessLoan_read (by decide)
      (by simp [sessionCtx, sessionCtxL, rootCtx, extendTy, midName, tailName, outName,
        sessionName])
      (by simp [VEnv.extend, rootEnv, sessionName, midName, tailName, outName])
      (TreeOwn.obs (Obs.var outName (by
        simp [obsEnv, sessionCtx, sessionCtxL, rootCtx, extendTy, midName, tailName, outName,
          sessionName]) Fragment.nat) siblingAccount_valid sessionCtx_handleWF.extendTy_obs))

/-
The session's read of the left leaf, evaluated: the real interpreter returns the
detached observation the reader holds.
-/
#guard decide (evalTree siblingLayout witnessState readProgram = some (.con0 7))

/-- The session's read, with the copying side given: the real `evalTree`'s detached
value is the value the *existing* `StepStar` of the program's instance reaches. -/
theorem session_read_agrees
    (hs : StepStar (inst (rootEnv siblingLayout witnessState) readProgram) (.con0 7)) :
    evalTree siblingLayout witnessState readProgram = some (.con0 7) :=
  evalTree_sound session_read_admitted hs (Value.con0 7)

/-- The session's read reaches a detached value the same reduction reaches: the
simulation's totality applied to the admitted derivation. -/
theorem session_read_total :
    ∃ v, evalTree siblingLayout witnessState readProgram = some v
      ∧ StepStar (inst (rootEnv siblingLayout witnessState) readProgram) v ∧ Value v :=
  evalTree_total session_read_admitted

/-- The session's detached read carries no protected node: the value the read hands
on is an observation. -/
theorem session_read_detached : hasProtected (.con0 7) = false :=
  quoteEl_hasProtected .nat 7

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

/-
The sequential hand-off, evaluated: the real interpreter returns the second
write's observation.
-/
#guard decide (evalTree (.leaf .nat) 7
  (.bind nextName (.store (.var cellName) 0 (.con0 5)) (.store (.var nextName) 0 (.con0 6)))
  = some (.con1 rootTag (.con0 6)))

/-- The sequential hand-off, at the boundary: the real `evalTree` agrees with the
*existing* `StepStar` of the program's instance at the value both reach. -/
theorem session_handoff_agrees
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
theorem session_handoff_total :
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
    nodeVal pairRight ((5, 9) : State pairLayout) = nodeVal pairRight pairState :=
  replaceAt_nodeVal_of_disjoint pairLeft pairRight 5 pairState rfl
    (disjoint_left_right (.here : Path (.leaf .nat)) (.here : Path (.leaf .nat)))

/-- The replacement lands its new focus where the path points. -/
theorem replacement_lands_check : subAt pairLeft ((5, 9) : State pairLayout) = 5 :=
  replaceAt_subAt pairLeft 5 pairState rfl

/-- The array's take-out and put-back equation at one level. -/
theorem takeout_level_check :
    replaceAt arrLayout (.index 1 (.here : Path (.leaf .nat))) (5 : State (.leaf .nat))
        (#[1, 2, 3] : Array (State (.leaf .nat)))
      = some ((#[1, 2, 3] : Array (State (.leaf .nat))).set 1 (5 : State (.leaf .nat))
          (by decide)) := by
  simp only [arrLayout]
  rw [replaceAt_index 1 (Path.here : Path (.leaf .nat)) 5 _ (by decide)]
  rfl

-- The take-out's conditional injectivity, as the library states it: the run's
-- counting and the coupling's counting of one heap are its two premises.
#check @Scidonia.RC.TreeOwnership.takeout_transfer

-- The interpreter and the agreement, as the library states them.
#check @evalTree_sound
#check @evalTree_sound_closed
#check @evalTree_total
#check @evalTree_no_protected
#check @runTreeIO_of_evalTree

/-! ## The executable takes no account

The guarantee the account carries is that no authority representation reaches the
executable: the account and its conditions are proof-side, and what a caller runs
is handed the layout's state and the term and nothing else. The checks below read
that off the executable's own surface.

`runTree` is the interpreter, and it is private, so an outside client cannot name
it — the refused lookup below is that failure — and its own signature is not
readable here. The surface a client does reach is `evalTree`, and the message
pinned first is its signature: the layout, the state and the term, and no account.
`#guard_msgs` compares the whole of the message, so an argument added, dropped or
retyped — an `Account` among them — fails the build. The second pin is the
boundary itself: the application with an account in the state's position does not
elaborate. The control beside that refusal is the same application with the state
in that position, which the session checks above already evaluate.
-/

/--
info: Scidonia.RC.TreeOwnership.evalTree (d : Layout) (s : State d) (e : Expr) : Option Expr
-/
#guard_msgs (whitespace := lax) in
#check Scidonia.RC.TreeOwnership.evalTree

-- The interpreter itself is private: an outside client cannot name it.
/--
info: Unknown identifier `Scidonia.RC.TreeOwnership.runTree`
-/
#guard_msgs (whitespace := lax) in
#check_failure Scidonia.RC.TreeOwnership.runTree

/--
info: Application type mismatch: The argument
  siblingAccount
has type
  Account siblingLayout
but is expected to have type
  State siblingLayout
in the application
  evalTree siblingLayout siblingAccount
-/
#guard_msgs (whitespace := lax) in
#check_failure (evalTree siblingLayout siblingAccount witnessState siblingProgram)

-- The control beside the refusal: the state in the state's position elaborates.
#check (evalTree siblingLayout witnessState siblingProgram)

/-! ## Axioms

Each of these is asserted: the `#guard_msgs` pins the list `#print axioms` emits,
so a proof that acquires another axiom fails the build rather than printing a
longer list for a reader. -/

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

/-- info: 'Scidonia.RC.TreeOwnership.lend_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.lend_valid

/-- info: 'Scidonia.RC.TreeOwnership.repay_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.repay_valid

/-- info: 'Scidonia.RC.TreeOwnership.fork_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.fork_valid

/-- info: 'Scidonia.RC.TreeOwnership.heldAt_lend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.heldAt_lend

/-- info: 'Scidonia.RC.TreeOwnership.heldAt_repay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.heldAt_repay

/-- info: 'Scidonia.RC.TreeOwnership.heldAt_fork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.heldAt_fork

/-- info: 'Scidonia.RC.TreeOwnership.treeOwn_validAccount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.treeOwn_validAccount

/-- info: 'Scidonia.RC.TreeOwnership.treeOwn_handleWF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.treeOwn_handleWF

/-- info: 'Scidonia.RC.TreeOwnership.treeOwn_store_handle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.treeOwn_store_handle

/-- info: 'Scidonia.RC.TreeOwnership.aliasCtx_not_handleWF' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.aliasCtx_not_handleWF

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

/-- info: 'Scidonia.RC.TreeOwnership.cell_spent_write_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.cell_spent_write_refused

/-- info: 'Scidonia.RC.TreeOwnership.cell_handoff_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.cell_handoff_admitted

/-- info: 'Scidonia.RC.TreeOwnership.cell_two_name_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.cell_two_name_refused

/-- info: 'Scidonia.RC.TreeOwnership.sub_out_of_bounds_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.sub_out_of_bounds_refused

/-- info: 'Scidonia.RC.TreeOwnership.sub_in_bounds_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.sub_in_bounds_admitted

/-- info: 'Scidonia.RC.TreeOwnership.replaceAt_inBounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.replaceAt_inBounds

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

/-- info: 'ScidoniaTest.TreeOwnership.session_write_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.TreeOwnership.session_write_admitted

/-- info: 'ScidoniaTest.TreeOwnership.session_write_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.TreeOwnership.session_write_total

/-- info: 'ScidoniaTest.TreeOwnership.session_read_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.TreeOwnership.session_read_admitted

/-- info: 'ScidoniaTest.TreeOwnership.session_read_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.TreeOwnership.session_read_total

/-- info: 'Scidonia.RC.TreeOwnership.rootCtx_handleWF' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.rootCtx_handleWF

/-- info: 'Scidonia.RC.TreeOwnership.multiAccount_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.multiAccount_valid

/-- info: 'Scidonia.RC.TreeOwnership.join_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.join_valid

/-- info: 'Scidonia.RC.TreeOwnership.heldAt_fork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.heldAt_fork

/-- info: 'Scidonia.RC.TreeOwnership.cell_two_name_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.cell_two_name_control

/-- info: 'Scidonia.RC.TreeOwnership.replaceAt_index' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.replaceAt_index

/-- info: 'Scidonia.RC.TreeOwnership.replaceAt_subAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.TreeOwnership.replaceAt_subAt

end ScidoniaTest.TreeOwnership
