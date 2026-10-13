/-
Checks for `Scidonia.RC.Transfer`, from outside the module.

The module is the transfer between the run model's configuration and the coupled
account: the run's handle list at a nested write and the coupling's split read the same
references, the take-out's check and the run's counting are the write theorem's two
named hypotheses, and the account's injectivity is a consequence of the two countings
rather than an input. A proof development has no pre-fix behaviour to observe, so the
checks here meet the transfer from outside, on heaps, handle lists and accounts a client
can build. They are of five kinds:

* **The transfer at one configuration, evaluated**, as `#guard`s: the run's handle list
  at the take-out and the coupling's split agree at every reference, the extracted
  occurrence is the run's head and is not named by the run's tail, the take-out's check
  passes at it, and the write's heap reads the same at the run's list as at the
  coupling's split and lands the written slots at the extracted occurrence. Each guard
  stands beside a control of the same shape whose message is pinned, so a guard is shown
  to fire rather than to pass whatever it is given.
* **The transfer's statements, applied**: the coupling at the run's tail and the account
  the take-out extracted is counted at the same heap as the run's own list is, and the
  composition reads the write's destructive branch off the take-out's check — at the run's
  own handle list, again at that list through `Scidonia.RC.store_destructive_of_corr` with
  the correspondence's name counts alone and no injectivity proof beside them, and at
  `Scidonia.RC.store_destructive_of_typed`'s coupling.
* **The boundary**, as theorems: the run's handle list is the coupling's split exactly at
  the empty account, the two accounts the run's side cannot separate --- the same
  references, hence the same counts at one heap and one handle list --- differ only in
  injectivity, and the account the take-out extracted is injective, which is the
  affirmative side of the clause `Scidonia.RC.Correspondence` names as the one neither
  the typing nor the coupling supplies.
* **A run's write step, read through the coupling**, as the module's own theorems applied at
  a step of `Run.writeStep`: the heap the step's take-out leaves is the one the transfer's
  configuration is read at, the coupling holds at it for the account that names the extracted
  occurrence, the composition gives the destructive branch at the nested subject beside the
  step's own result, and the boundary statement says what a coupling at the run's own handle
  list leaves.
* **Axioms**: each representative theorem's `#print axioms` output is pinned, so a proof
  that acquires an axiom it should not fails the build rather than printing a longer list
  for a reader to notice. The lists that name `Classical.choice` are those that read a
  membership out of its absence through the counted heap's `Classical.byContradiction`
  lemmas, which is where it comes in.

The heaps below are read as exactly the cells they list, which is the reading `Counted`
is stated under; nothing here constructs a heap from a compiled run.
-/
import Scidonia.RC.Transfer
import ScidoniaTest.Run

open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap
open Scidonia.FracPerm.StateVar.Run
open Scidonia.RC

namespace ScidoniaTest.Transfer

/-! ## The configuration the transfer is read at

The run has walked the chain's root path: the take-out has emptied the root's only slot
and holds the occurrence it extracted, so the run's handle list is the extracted
occurrence followed by the runner's own handle, and the coupling's split is the runner's
handle followed by the account's one occurrence. -/

/-- The chain's heap after the take-out: the root's slot is emptied and the cell it
named is untouched. -/
def held : CHeap :=
  [(0, { slots := [], count := 1 }), (1, { slots := [2], count := 1 }),
    (2, { slots := [], count := 1 })]

/-- The run's handle list at the nested focus check: the extracted occurrence at the
head, the runner's own handle on the root behind it. -/
def taken : List Ref := [1, 0]

/-- The coupling's run handles: the runner's own handle alone, the extracted occurrence
being the account's. -/
def rest : List Ref := [0]

/-- The account: the occurrence the take-out extracted, read at the subject's name. -/
def acct : Multi := [(0, 1)]

/-- The environment: the subject's name bound to the extracted reference. -/
def env : TEnv := [(0, 1)]

/-- The typing's environment at the store's own position: the subject's name held
once. -/
def occs : Occs := [0]

/-! ## The split, the check and the write's result, evaluated -/

/-
The take-out's two lists read the same counts: the extracted occurrence is the run's
head, the run's tail does not name it, and the coupling's split counts it the one time
the run's head does.
-/
#guard decide ((expand acct).count 1 = 1)

/--
error: Expression
  decide (List.count 1 (expand acct) = 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((expand acct).count 1 = 2)

/--
error: Expression
  decide (List.count 1 [1, 0] = 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((1 :: [0] : List Ref).count 1 = 2)

/--
error: Expression
  decide (List.count 1 [0] = 1)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (([0] : List Ref).count 1 = 1)

/--
error: Expression
  decide (List.count 1 [1, 0] = 0)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((1 :: [0] : List Ref).count 1 = 0)

/--
error: Expression
  decide (List.count 0 [1, 0] = 0)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((1 :: [0] : List Ref).count 0 = 0)

/-
The two lists the transfer relates count alike: the run's handle list names the extracted
occurrence at its head and the runner's handle behind it, and the coupling's split names
the runner's handle and the account's one occurrence, which is the extracted reference.
-/
#guard decide ((1 :: [0] : List Ref).count 1 = ([0] ++ expand acct).count 1)
#guard decide ((1 :: [0] : List Ref).count 0 = ([0] ++ expand acct).count 0)

/--
error: Expression
  decide (List.count 1 ([0] ++ expand acct) = 0)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (([0] ++ expand acct).count 1 = 0)

/--
error: Expression
  decide (List.count 0 ([0] ++ expand acct) = 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (([0] ++ expand acct).count 0 = 2)

/-
The take-out's check at the extracted occurrence passes: the cell is named by that one
handle and by no slot.
-/
#guard decide (exclusive? held taken 1 = true)

/--
error: Expression
  decide (exclusive? held taken 1 = false)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (exclusive? held taken 1 = false)

/-
The write's heap does not depend on the handle list it was handed, and it lands the
written slots at the extracted occurrence: the addressed cell holds the write's slots and
the cell its emptied slot named is freed by the cascade.
-/
#guard decide ((update held (1 :: [0]) 1 []).1 = (update held ([0] ++ expand acct) 1 []).1)
#guard decide ((update held ([0] ++ expand acct) 1 []).1.lookup 1 = some [])

/--
error: Expression
  decide ((update held [1, 0] 1 []).fst = (update held ([0] ++ expand acct) 1 [2]).fst)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((update held (1 :: [0]) 1 []).1 = (update held ([0] ++ expand acct) 1 [2]).1)

/--
error: Expression
  decide ((update held ([0] ++ expand acct) 1 []).fst.lookup 1 = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((update held ([0] ++ expand acct) 1 []).1.lookup 1 = none)

/--
error: Expression
  decide ((update held [1, 0] 1 []).fst = held)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((update held (1 :: [0]) 1 []).1 = held)

/-! ## The counting at the run's list and at the coupling's split -/

/-- The run's configuration is counted at its own handle list. -/
theorem taken_counted : Counted held taken := by
  refine ScidoniaTest.Run.counted_of held taken ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by simpa [held] using hx
    rcases hx' with rfl | rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 2 := by simpa [held] using hx
    rw [hx']
    decide
  · intro x hx
    simp only [taken, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide

/-- The same heap is counted at the coupling's split: the run's handles with the
account's occurrence after them. -/
theorem split_counted : Counted held (rest ++ expand acct) := by
  refine ScidoniaTest.Run.counted_of held (rest ++ expand acct) ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by simpa [held] using hx
    rcases hx' with rfl | rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 2 := by simpa [held] using hx
    rw [hx']
    decide
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with h1 | h2
    · have hx' : x = 0 := by simpa [rest] using h1
      rw [hx']
      decide
    · have hx' : x = 1 := by simpa [acct, expand] using h2
      rw [hx']
      decide

/-- The transferred counting: the coupling's counting follows from the run's, the
account being the occurrence the take-out extracted. -/
theorem transfer_transfers_counting : Counted held (rest ++ expand acct) :=
  counted_couple_of_takeout taken_counted (by decide)

/-- The take-out's check at the extracted occurrence: the cell is named by that one
handle and by no slot. -/
theorem takeout_exclusive : Exclusive (CHeap.presentation held) taken 1 :=
  exclusive?_eq_true (by decide)

/-- The take-out's check decides the write's branch: the update is the counted heap's
destructive one. -/
theorem takeout_write_destructive :
    update held taken 1 [] = (CHeap.cascade (CHeap.writeSlots held 1 []), taken) :=
  takeout_update_destructive taken_counted takeout_exclusive

/-! ## The coupling and the composition -/

/-- The heap is well formed. -/
theorem held_wf : CHeap.WF held := by rw [CHeap.WF]; decide

/-- Every pair of the account names the reference the environment binds its name to. -/
theorem env_bound : Bound env acct := by
  intro p hp
  have hp' : p = (0, 1) := by simpa [acct] using hp
  rw [hp']
  rfl

/-- The coupling at the run's tail and the occurrence the take-out extracted. -/
theorem held_couple : Couple held rest env acct := ⟨held_wf, split_counted, env_bound⟩

/-- The account's multiplicity at each name is the typing's count of that name. -/
theorem acct_names : ∀ x, countName acct x = occs.count x := by
  intro x
  rw [countName_eq_count_fst]
  simp [acct, occs]

/-- The correspondence at the take-out's configuration: the environment clauses hold,
and the injectivity is the one occurrence's. -/
theorem acct_corr : Corr env acct occs := by
  refine ⟨env_bound, acct_names, ?_⟩
  intro p hp q hq _
  have hp' : p = (0, 1) := by simpa [acct] using hp
  have hq' : q = (0, 1) := by simpa [acct] using hq
  rw [hp', hq']

/-- The store the composition reads, typed at the account's own environment: its
subject's name is owned exactly once there and not borrowed. -/
theorem store_typed : Typed ([] : Occs) occs (.store (.var 0) 0 (.con0 9)) := by
  refine Typed.store (hown := by decide) (hborrow := by decide) ?_
  exact Typed.con0

/-- The subject's name reads back the extracted reference. -/
theorem env_lookup : env.lookup 0 = some 1 := by decide

/-- The composition at the take-out's configuration: the run's counting beside the
take-out's check gives the write theorem's two hypotheses, and the write is destructive
at the extracted occurrence. -/
theorem transfer_at_a_run : (update held taken 1 []).1.lookup 1 = some [] :=
  store_destructive_of_takeout held_couple taken_counted takeout_exclusive acct_names
    env_lookup store_typed (by decide)

/-- The same write read at the coupling's own split: `store_destructive_of_typed` at the
same configuration, whose two named hypotheses the take-out supplies. -/
theorem coupled_write_destructive :
    (update held (rest ++ expand acct) 1 []).1.lookup 1 = some [] :=
  store_destructive_of_typed held_couple acct_corr env_lookup store_typed (by decide)
    (by decide) (by decide)

/-- The same write through the correspondence's own vocabulary: `store_destructive_of_corr`
takes the correspondence's name counts and builds the `Corr` itself --- the injectivity
the structure carries is the consequence `refInj_of_counted` reads off the run's counting
and the coupling's --- so no injectivity proof is built here. -/
theorem corr_write_destructive : (update held taken 1 []).1.lookup 1 = some [] :=
  store_destructive_of_corr held_couple taken_counted takeout_exclusive acct_names
    env_lookup store_typed (by decide)

/-- The account the take-out extracted is injective: one occurrence's tags cannot
disagree. -/
theorem acct_inj : RefInj acct :=
  refInj_of_counted taken_counted split_counted

/-! ## The boundary -/

/-- The run's own handle list is the coupling's split at the empty account: the counts
agree. -/
theorem split_agrees_at_the_empty_account :
    ∀ x, ([0] ++ expand ([] : Multi)).count x = ([0] : List Ref).count x :=
  (count_split_agree_iff [0] []).mpr rfl

/-- The run's own handle list is not the coupling's split at an account that names a
reference: adding the account's occurrence moves the count at it. -/
theorem split_disagrees_at_one_occurrence :
    ¬ (∀ x, ([0] ++ expand acct).count x = ([0] : List Ref).count x) :=
  fun h => by
    have hz := (count_split_agree_iff [0] acct).mp h
    simp [acct] at hz

/-- Two accounts the run's side cannot tell apart: the same references, hence the same
count at every heap and handle list. -/
theorem boundary_accounts :
    expand ([(0, 0), (0, 0)] : Multi) = expand ([(0, 0), (1, 0)] : Multi) := rfl

/-- The affirmative counterpart of the refutation: the account whose pairs name one
reference at one name is injective, whatever its references are. -/
theorem repeated_pair_inj : RefInj ([(0, 0), (0, 0)] : Multi) := by
  intro p hp q hq _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rfl

/-- The two accounts at one heap and one handle list: both are counted there, so the
run's side sees the same configuration, and only the tags differ --- one of them naming
the reference twice. -/
theorem boundary_at_one_configuration :
    Counted ScidoniaTest.Run.pair ([] ++ expand ([(0, 0), (1, 0)] : Multi))
      ∧ Counted ScidoniaTest.Run.pair ([] ++ expand ([(0, 0), (0, 0)] : Multi))
      ∧ RefInj ([(0, 0), (0, 0)] : Multi) ∧ ¬ RefInj ([(0, 0), (1, 0)] : Multi) :=
  ⟨by simpa [expand] using ScidoniaTest.Run.pair_counted,
    by simpa [expand] using ScidoniaTest.Run.pair_counted, repeated_pair_inj,
    by simpa [aliasM] using alias_not_inj⟩

/-! ## A run's write step, read through the coupling

The heap above is the configuration a write step's take-out leaves at the chain: the step at
the chain's first path takes the middle cell out of the root's slot, drops the pair's handle,
and checks the extracted cell, so the configuration it hands the nested write is that
take-out's — the heap above and the extracted occurrence at the head of the runner's handle
list. The checks below pin that identification, and the transfer's statements are then read at
the step rather than at a heap built by hand. -/

/-- The run model's own take-out at the chain's root slot leaves the heap above: the
transfer's configuration is the one `Run.writeStep`'s recursion enters, not a heap a client
composed. -/
theorem step_takeout_is_held :
    Scidonia.FracPerm.StateVar.Run.held ScidoniaTest.Run.chain 0 0 1 = held ∧
      (CHeap.slotsAt ScidoniaTest.Run.chain 0)[0]? = some 1 ∧
      1 :: ScidoniaTest.Run.handles = taken :=
  ⟨by decide, by decide, by decide⟩

/-- The coupling at the configuration the write step's take-out hands the nested write: the
run's counting at the chain beside the root's focus check, and the account naming the
occurrence the take-out extracted. -/
theorem held_couple_of_the_step : Couple held rest env acct :=
  couple_of_takeout (c := ScidoniaTest.Run.chain) (hs := ScidoniaTest.Run.handles) (r := 0)
    (i := 0) (e := 1) ScidoniaTest.Run.chain_wf ScidoniaTest.Run.chain_counted
    (by decide) (exclusive?_eq_true (by decide)) (by decide) env_bound (by decide)

/-- The composition at the run's own write step: the step at the chain's first path, with the
result `Run.writeStep_spec` gives it, and the destructive branch at the nested subject read
through the correspondence the coupling and the two countings build. -/
theorem writeStep_chain_nested_destructive :
    Couple held rest env acct ∧
      (update held taken 1 []).1.lookup 1 = some [] ∧
      ScidoniaTest.Run.upper.lookup 1 = some [] := by
  have hstep : writeStep ScidoniaTest.Run.chain ScidoniaTest.Run.handles 0 [0] [] =
      some (ScidoniaTest.Run.upper, ScidoniaTest.Run.handles) := by decide
  have hlook : (CHeap.slotsAt ScidoniaTest.Run.chain 0)[0]? = some 1 := by decide
  obtain ⟨hcouple, hdest, _, t, ht, hl⟩ :=
    writeStep_nested_destructive_of_couple (root := 0) (c := ScidoniaTest.Run.chain)
      (hs := ScidoniaTest.Run.handles) (i := 0) (p := []) (ks := []) (e := 1)
      (c' := ScidoniaTest.Run.upper) (hs' := ScidoniaTest.Run.handles)
      ScidoniaTest.Run.chain_accept hstep hlook env_bound (by decide) (by decide)
      acct_names env_lookup store_typed
  have ht1 : t = 1 := by
    rw [show resolve ScidoniaTest.Run.chain 0 [0] = some 1 from by decide] at ht
    exact (Option.some.inj ht).symm
  exact ⟨hcouple, hdest, by rw [ht1] at hl; exact hl⟩

/-- The same composition at a write step whose path's level is its last: the recursion's
entry is the write's own subject, so the leaf's check supplies the write rule's premise on the
written slots and the run's result and the coupling's branch are about one cell. -/
theorem writeStep_chain_subject_destructive :
    Couple held rest env acct ∧
      (update held taken 1 []).1.lookup 1 = some [] ∧
      ScidoniaTest.Run.upper.lookup 1 = some [] :=
  writeStep_subject_destructive_of_couple (root := 0) (c := ScidoniaTest.Run.chain)
    (hs := ScidoniaTest.Run.handles) (i := 0) (ks := []) (e := 1)
    (c' := ScidoniaTest.Run.upper) (hs' := ScidoniaTest.Run.handles)
    ScidoniaTest.Run.chain_accept (by decide) (by decide) env_bound (by decide)
    acct_names env_lookup store_typed

/-- The boundary the account is read at, as a statement about every account: a coupling at
the run's own handle list names no occurrence, so the only account the chain's configuration
couples with there is the empty one. -/
theorem chain_couple_is_empty {ρ : TEnv} {m : Multi}
    (h : Couple ScidoniaTest.Run.chain ScidoniaTest.Run.handles ρ m) : m = [] :=
  couple_at_run_handles_is_empty ScidoniaTest.Run.chain_counted h

/-- The same boundary's affirmative side: the chain's own configuration couples with the
empty account, which is the one the statement above leaves. -/
theorem run_handles_couple_is_empty :
    Couple ScidoniaTest.Run.chain ScidoniaTest.Run.handles env [] := by
  refine ⟨ScidoniaTest.Run.chain_wf, ?_, ?_⟩
  · simpa using ScidoniaTest.Run.chain_counted
  · intro p hp
    simp at hp

/-! ## Axioms

Each representative theorem's list is pinned, so a proof that acquires an axiom it should
not fails the build rather than printing a longer list for a reader to notice; the
remaining new theorems of the module and of these checks are printed beside them. -/

/--
info: 'Scidonia.RC.store_destructive_of_takeout' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms store_destructive_of_takeout

/--
info: 'Scidonia.RC.refInj_not_determined' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refInj_not_determined

/--
info: 'Scidonia.RC.refInj_of_counted' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refInj_of_counted

/--
info: 'Scidonia.RC.counted_couple_of_takeout' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_couple_of_takeout

/--
info: 'Scidonia.RC.update_fst_eq_of_handles' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms update_fst_eq_of_handles

/--
info: 'Scidonia.RC.counted_split_congr' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_split_congr

/--
info: 'ScidoniaTest.Transfer.transfer_at_a_run' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms transfer_at_a_run

/--
info: 'ScidoniaTest.Transfer.taken_counted' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms taken_counted

/--
info: 'Scidonia.RC.couple_of_takeout' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms couple_of_takeout

/--
info: 'Scidonia.RC.writeStep_nested_destructive_of_couple' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms writeStep_nested_destructive_of_couple

/-! The remaining new theorems' lists -/

#print axioms count_self_eq_length_of_all_eq
#print axioms eq_singleton_of_count
#print axioms count_takeout_split
#print axioms counted_takeout_of_couple
#print axioms count_split_agree_iff
#print axioms takeout_update_destructive
#print axioms expand_eq_singleton_of_counted
#print axioms refInj_of_expand_singleton
#print axioms store_destructive_of_corr
#print axioms split_counted
#print axioms transfer_transfers_counting
#print axioms takeout_exclusive
#print axioms takeout_write_destructive
#print axioms held_wf
#print axioms env_bound
#print axioms held_couple
#print axioms acct_names
#print axioms acct_corr
#print axioms store_typed
#print axioms env_lookup
#print axioms coupled_write_destructive
#print axioms corr_write_destructive
#print axioms acct_inj
#print axioms split_agrees_at_the_empty_account
#print axioms split_disagrees_at_one_occurrence
#print axioms boundary_accounts
#print axioms repeated_pair_inj
#print axioms boundary_at_one_configuration

#print axioms couple_at_run_handles_is_empty
#print axioms writeStep_focus
#print axioms writeStep_recurses
#print axioms writeStep_subject_destructive_of_couple
#print axioms step_takeout_is_held
#print axioms held_couple_of_the_step
#print axioms writeStep_chain_nested_destructive
#print axioms writeStep_chain_subject_destructive
#print axioms chain_couple_is_empty
#print axioms run_handles_couple_is_empty

end ScidoniaTest.Transfer
