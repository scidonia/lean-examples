/-
Checks for `Scidonia.RC.Correspondence`, from outside the module.

The module is the link between the typing's environments and the target's account: the
correspondence `Corr`, under which a store's own write clause gives the two premises
`Scidonia.RC.store_owned_is_destructive` consumes, and the composition that reads the
write theorem's branch off them. A proof development has no pre-fix behaviour to
observe, so the checks here meet the correspondence from outside, on heaps, terms and
accounts a client can build. They are of seven kinds:

* **The configuration the lowering's run reaches, the write it installs and the
  counts, evaluated**, as `#guard`s: the run's third step is the configuration the
  bridge is read at, the write the run installs at the allocated cell is the store's
  slot list, the account's multiplicities at its names, and the counts at the
  references the run holds. Each guard stands beside a control of the same shape whose
  message is pinned, so a guard is shown to fire rather than to pass whatever it is
  given.
* **The readings of the typed source, and the reading a list of names is**, as
  theorems: the source's own occurrences are not the pairs its environment reads it at;
  the account a list of names reads as satisfies the coupling invariant's `Bound` and
  is one no account holding a name twice can be, so the reading the correspondence is
  not stated with is refused at the very configuration a binding would leave; and the
  account the lowering's prologue leaves passes the binding rule's own check where the
  source's does not.
* **The typing's environment at a store**, as theorems: its count of the subject's name
  there is one, and it is read per position, so the correspondence's name-count clause
  is read at the store's own environment and not at the program's.
* **The correspondence at the reachable configuration**, as a derivation:
  `corr_at_actual` reads the coupling invariant's `Bound`, the name counts and the
  injectivity off the account a lowered run's binding leaves.
* **The two routes at that configuration**: `runs_at_actual` and `bridge_at_actual` are
  the judgement of `Scidonia.RC.Discipline` at the configuration the run reaches --- the
  route `ScidoniaTest/Target`'s `lowered_not_runs` refuses one reference earlier --- and
  `bridge_at_reachable` is the correspondence's bridge there, the same `Owns` and the
  same count of one.
* **The composition, applied**: `reached_destructive` is
  `Scidonia.RC.store_destructive_of_typed` at that configuration, and the guards beside
  it read the heap the update leaves back at the heap the run leaves. The controls'
  affirmative counterparts are beside them: the accounts the lowering's prologue and the
  source's own environment leave are injective, and the typing refuses the sibling term
  whose account would hold a name twice.
* **Axioms**: each representative theorem's `#print axioms` output is pinned, so a proof
  that acquires an axiom it should not fails the build rather than printing a longer
  list for a reader to notice.

The heaps below are read as exactly the cells they list, which is the reading `Counted`
is stated under; nothing here constructs a heap from a compiled run.
-/
import Scidonia.RC.Correspondence
import ScidoniaTest.Target

open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap
open Scidonia.RC
open ScidoniaTest.Target

namespace ScidoniaTest.Correspondence

set_option synthInstance.maxSize 400

/-! ## The configuration the lowering's run reaches -/

/-- The heap the lowering's run holds when the binding that precedes the write has
resumed: the node the binding allocated at the fresh location `3`, with the fields'
references as its slots, the cell its first slot names, and the written value's
cell. -/
def reachHeap : CHeap :=
  [(3, { slots := [1, 2], count := 1 }), (1, { slots := [], count := 2 }),
    (2, { slots := [], count := 3 })]

/-- The environment the run holds there: the binding's binder names the allocated
node. -/
def reachEnv : TEnv := env0.set 0 3

/-- The account the run holds there: the source's own occurrences with the occurrence
the prologue's `dup` supplies --- the one its `drop` releases --- beside the occurrence
the binding's binder takes up at the allocated reference. -/
def reachAcct : Multi := [(0, 3), (2, 2), (1, 1), (2, 2)]

/-! ## The configuration, the write and the counts, evaluated -/

/-
The lowering's run reaches, at its third step, exactly the configuration `reachHeap`,
`reachEnv`, `reachAcct` and the store term denote: the prologue's `dup` and `drop` have
fired, the binding has allocated the node at `3` and the binder has taken up its handle,
and the write is the term in hand. The control beside it claims the same configuration
with the source term in place of the store, which the guard shows to fire.
-/
#guard decide (trun 3 (base, [], env0, pairsOf env0 ([0,1,2] : Occs), lowered)
  = (reachHeap, ([] : List Ref), reachEnv, reachAcct, storeTerm))

/--
error: Expression
  decide (trun 3 (base, [], env0, pairsOf env0 [0, 1, 2], lowered) =
      (reachHeap, [], reachEnv, reachAcct, source))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (trun 3 (base, [], env0, pairsOf env0 ([0,1,2] : Occs), lowered)
  = (reachHeap, ([] : List Ref), reachEnv, reachAcct, source))

/-
The write the run installs at the allocated cell is the store's slot list: the cell's
first slot, which named the reference `1`, is set to the reference the written value
names, and the write's own check accepts the list. The control beside them is the
cell's slots as they were.
-/
#guard decide (storeSlots reachHeap 3 0 2 = [2, 2])
#guard decide (writeCheck reachHeap 3 [2, 2])

/--
error: Expression
  decide (storeSlots reachHeap 3 0 2 = [1, 2])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (storeSlots reachHeap 3 0 2 = [1, 2])

/-
The account's multiplicities at its names, and the counts at the references the run
holds: the subject's name is held once, the written value's name twice, the binder's
cell once, and the reference the write lands at exactly once --- the count the write
theorem reads. The controls beside them are counts of the same account that no reading
gives.
-/
#guard decide (countName reachAcct 0 = 1 && countName reachAcct 1 = 1 && countName reachAcct 2 = 2)
#guard decide ((expand reachAcct).count 3 = 1 && (expand reachAcct).count 2 = 2)
#guard decide ((expand reachAcct).count 0 = 0)

/--
error: Expression
  decide (List.count 3 (expand reachAcct) = 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((expand reachAcct).count 3 = 2)

/--
error: Expression
  decide (countName reachAcct 2 = 1)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (countName reachAcct 2 = 1)

/-
The counterexample's readings, evaluated: the two names `0` and `1` both name the
reference `0`, so each name's multiplicity is one while the reference's count is two.
The control beside them is the reference counted once, which the same account does not
give.
-/
#guard decide (countName aliasM 0 = 1 && countName aliasM 1 = 1)
#guard decide ((expand aliasM).count 0 = 2)

/--
error: Expression
  decide (List.count 0 (expand aliasM) = 1)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((expand aliasM).count 0 = 1)

/-
The update the store's destructive branch performs is the heap the run leaves: the cell
at `3` holds the written slots, the cell the emptied slot named is freed, and the written
value's cell carries the new cell's occurrences. The control beside it is the cell's
slots as they were, which the run does not leave.
-/
#guard decide ((update reachHeap ([] ++ expand reachAcct) 3 [2, 2]).1.lookup 3 = some [2, 2])
#guard decide ((update reachHeap ([] ++ expand reachAcct) 3 [2, 2]).1
  = (trun 4 (base, [], env0, pairsOf env0 ([0,1,2] : Occs), lowered)).1)

/--
error: Expression
  decide ((update reachHeap ([] ++ expand reachAcct) 3 [2, 2]).fst.lookup 3 = some [1, 2])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((update reachHeap ([] ++ expand reachAcct) 3 [2, 2]).1.lookup 3 = some [1, 2])

/-! ## The readings of the typed source -/

/-- The source's own occurrences are not the pairs its environment reads it at: the two
readings of the account differ even at the typed source, which is the first reason the
correspondence is stated with the account's own name counts rather than with a
computation on the term's free variables. -/
theorem source_readings_differ : occsOf env0 source ≠ pairsOf env0 ([0,1,2] : Occs) := by
  decide

/-- The account the source's environment reads the term as fails the binding rule's own
check at the binder `0`: the rule asks the binder's name to be one the account holds
nowhere at another reference, and that account holds `0`. -/
theorem source_account_not_freeName : freeName (pairsOf env0 ([0,1,2] : Occs)) 0 = false := by
  decide

/-- The account the lowering's prologue leaves passes that check: the prologue's release
is the omission the binding rule demands, and it is what the *lowering* costs rather
than what the source's own environment says. -/
theorem prologue_account_freeName : freeName prologueAcct 0 = true := by
  decide

/-- The account a `bindVal` step *would* leave, if it fired, is mis-tagged: the stale
occurrence `(0, 0)` sits beside the binder's `(0, 3)`, and the environment names `0` at
`3` from then on. The binding rule's own check refuses the configuration before any step
--- the refusal above --- and the point recorded here is that the reading a list of
names gives is not even a pre-step invariant at the binder's name. -/
theorem bindVal_account_not_pairsOf :
    ¬ Bound (env0.set 0 3) ([(0,3),(0,0),(1,1),(2,2)] : Multi) := by
  intro h
  have h1 : (env0.set 0 3).lookup (0 : Var) = some (0 : Ref) := h (0, 0) (by decide)
  exact absurd h1 (by decide)

/-- The account above is no `pairsOf` reading of any list of names at the environment a
binding leaves: every account a list of names reads as satisfies `Bound`, so the account
a binding would leave is not one that reading can produce. -/
theorem bindVal_account_not_pairsOf_any (Γ : Occs) :
    ([(0,3),(0,0),(1,1),(2,2)] : Multi) ≠ pairsOf (env0.set 0 3) Γ := by
  intro h
  exact bindVal_account_not_pairsOf (h ▸ pairsOf_bound (env0.set 0 3) Γ)

/-! ## The typing's environment at the source's store -/

/-- The typing's environment at the source's store position counts the subject's name
once: the count the bridge reads, at the position the store actually is. -/
theorem source_store_env_count :
    (bindEnv ([0,1,2] : Occs) 0 (uses (.store (.var 0) 0 (.var 2)))).count 0 = 1 := by
  decide

/-- The typing's environment at a store is *positional*: `claimEnv` splits it per
position, so a store's own environment counts its subject's name once even when the
enclosing program mentions it twice. The correspondence's name-count clause is therefore
read at the store's own `Γ` and not at the program's. -/
theorem sibling_positional :
    claimEnv ([0,0] : Occs) (uses (.store (.var 0) 0 (.con0 9))) = [0]
      ∧ ([0,0] : Occs).count 0 = 2 := ⟨by decide, by decide⟩

/-! ## The correspondence, and the two routes, at the reachable configuration -/

/-- The correspondence holds at the configuration the lowering's run reaches: every
pair of the account names the reference the environment binds its name to, the account's
multiplicity at each name is the typing's count of that name at `[0, 1, 2, 2]` --- the
source's environment with the occurrence the prologue supplied --- and the account's tags
are injective on references. -/
theorem corr_at_actual : Corr reachEnv reachAcct ([0,1,2,2] : Occs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have hp' : p = (0, 3) ∨ p = (2, 2) ∨ p = (1, 1) ∨ p = (2, 2) := by
      simpa [reachAcct] using hp
    rcases hp' with rfl | rfl | rfl | rfl <;> decide
  · intro x
    rw [countName_eq_count_fst]
    change (([0,2,1,2] : List Var)).count x = (([0,1,2,2] : List Var)).count x
    by_cases h0 : x = 0
    · subst h0; decide
    by_cases h1 : x = 1
    · subst h1; decide
    by_cases h2 : x = 2
    · subst h2; decide
    · have e1 : (([0,2,1,2] : List Var)).count x = 0 :=
        List.count_eq_zero.mpr (by simp [h0, h1, h2])
      have e2 : (([0,1,2,2] : List Var)).count x = 0 :=
        List.count_eq_zero.mpr (by simp [h0, h1, h2])
      rw [e1, e2]
  · intro p hp q hq heq
    have hp' : p = (0, 3) ∨ p = (2, 2) ∨ p = (1, 1) ∨ p = (2, 2) := by
      simpa [reachAcct] using hp
    have hq' : q = (0, 3) ∨ q = (2, 2) ∨ q = (1, 1) ∨ q = (2, 2) := by
      simpa [reachAcct] using hq
    rcases hp' with rfl | rfl | rfl | rfl <;>
      rcases hq' with rfl | rfl | rfl | rfl <;> simp_all

/-- The judgement of `Scidonia.RC.Discipline` at that configuration: the store's clause
is met at the reference the binding realised, which is the configuration the run reaches.
The judgement is *not* derived one reference earlier, at the reference the prologue's
account counts three times --- `ScidoniaTest/Target`'s `lowered_not_runs` --- so this is
the route's own reach. -/
theorem runs_at_actual : Runs reachEnv reachAcct storeTerm := by
  refine Runs.store (ρ := reachEnv) (y := 0) (i := 0) (v := .var 2) (m := reachAcct)
    (Owns.store (hρ := TEnv.lookup_set_self env0 0 3) (hmem := by decide)) ?_ ?_ ?_
  · intro r hr
    have hr3 : r = 3 := Option.some.inj (hr.symm.trans (TEnv.lookup_set_self env0 0 3))
    rw [hr3]
    decide
  · exact Runs.var (x := 2) (r := 2) (hρ := by decide) (hmem := by decide)
  · exact Runs.var (x := 0) (r := 3) (hρ := TEnv.lookup_set_self env0 0 3) (hmem := by decide)

/-- The store's two hypotheses read off that judgement: the account holds the subject's
occurrence, and the reference the environment names for it is counted once. -/
theorem bridge_at_actual :
    Owns reachEnv reachAcct storeTerm
      ∧ ∃ r, reachEnv.lookup 0 = some r ∧ (expand reachAcct).count r = 1 :=
  runs_store_owned runs_at_actual

/-- The correspondence's bridge at the same configuration: the same `Owns` and the count
of one at the realised reference `3`, read from the correspondence and the store's own
write clause rather than from a judgement of the target's relation. -/
theorem bridge_at_reachable :
    Owns reachEnv reachAcct storeTerm ∧ (expand reachAcct).count (3 : Ref) = 1 :=
  bridge (ρ := reachEnv) (m := reachAcct) (Γ := [0,1,2,2]) corr_at_actual
    (TEnv.lookup_set_self env0 0 3) (by decide)

/-! ## The composition, applied at the reachable configuration -/

/-- The account counts the reference the write lands at exactly once, read through the
reference-count reading `count_expand` gives. -/
theorem reach_ref_count_one : (expand reachAcct).count (3 : Ref) = 1 := by
  rw [count_expand]
  decide

/-- The reachable configuration satisfies the coupling invariant: the heap is well
formed, its counts are the account's own references at the run's empty handles, and
every pair of the account names the reference the environment binds its name to. -/
theorem reached_couple : Couple reachHeap [] reachEnv reachAcct := by
  refine ⟨?_, ?_, ?_⟩
  · rw [CHeap.WF]; decide
  · refine counted_of reachHeap [3, 2, 1, 2] ?_ ?_ ?_
    · intro x hx
      have hx' : x = 3 ∨ x = 1 ∨ x = 2 := by simpa [reachHeap] using hx
      rcases hx' with rfl | rfl | rfl <;> decide
    · intro x hx
      have hx' : x = 1 ∨ x = 2 := by simpa [reachHeap] using hx
      rcases hx' with rfl | rfl <;> decide
    · intro x hx
      have hx' : x = 3 ∨ x = 2 ∨ x = 1 ∨ x = 2 := by simpa using hx
      rcases hx' with rfl | rfl | rfl | rfl <;> decide
  · intro p hp
    have hp' : p = (0, 3) ∨ p = (2, 2) ∨ p = (1, 1) ∨ p = (2, 2) := by
      simpa [reachAcct] using hp
    rcases hp' with rfl | rfl | rfl | rfl <;> decide

/-- The store the composition reads, typed at the account's own environment `[0, 1, 2,
2]`: its subject's name is owned exactly once there and not borrowed, and its written
value is a variable. -/
theorem reach_store_typed :
    Typed ([] : Occs) ([0,1,2,2] : Occs) (.store (.var 0) 0 (.var 2)) := by
  refine Typed.store (hown := by decide) (hborrow := by decide) ?_
  exact Typed.var (Or.inl (by decide))

/-- The composition at the configuration the lowering's run reaches: the store of the
typed source is destructive there, so the cell the binder took up keeps its location and
holds the written slots. The guards above read the same update's heap back at the heap
the run leaves, and `ScidoniaTest/Target`'s `source_typed` is the typing the composition
reads its write clause from. -/
theorem reached_destructive :
    (update reachHeap ([] ++ expand reachAcct) 3 [2, 2]).1.lookup 3 = some [2, 2] :=
  store_destructive_of_typed reached_couple corr_at_actual (TEnv.lookup_set_self env0 0 3)
    reach_store_typed (by decide) (by decide) (by decide)

/-! ## The controls' affirmative counterparts -/

/-- The account the lowering's prologue leaves is injective: the `dup` the prologue
supplies names a reference the account already holds and is removed from the source's
account by the `drop`, so what is left names each of its references at one name. It is
the affirmative side of the negative controls in the module. -/
theorem prologueAcct_refInj : RefInj prologueAcct := by
  have h : prologueAcct = ([(2,2),(1,1),(2,2)] : Multi) := by decide
  rw [h]
  intro p hp q hq heq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> simp_all

/-- The account the source's own environment reads the term as is injective too: the
negative controls are about a configuration the typing admits and the coupling invariant
does not refuse, not about every account. -/
theorem pairsOf_env0_refInj : RefInj (pairsOf env0 ([0,1,2] : Occs)) := by
  have h : pairsOf env0 ([0,1,2] : Occs) = ([(0,0),(1,1),(2,2)] : Multi) := by decide
  rw [h]
  intro p hp q hq heq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> simp_all

/-- The typing refuses the sibling term whose account would hold the subject's name
twice: the term writes through the name its binder carries and uses that name in a
sibling position, so the name is not the write's only occurrence and the program has no
typing at the empty environments. Together with the injectivity claims above it is the
affirmative side of the negative controls: the configuration that would leave two names
at one reference is not one the typing reaches. -/
theorem sibling_refused : ¬ Typed ([] : Occs) ([] : Occs) siblingUse :=
  sibling_use_no_typing

/-! ## Axioms

Each representative theorem's list is pinned, so a proof that acquires an axiom it
should not fails the build rather than printing a longer list for a reader to notice;
the remaining new theorems of the module and of these checks are printed beside them.
-/

/--
info: 'Scidonia.RC.bridge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bridge

/--
info: 'Scidonia.RC.store_destructive_of_typed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms store_destructive_of_typed

/--
info: 'ScidoniaTest.Correspondence.corr_at_actual' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms corr_at_actual

/--
info: 'ScidoniaTest.Correspondence.reached_destructive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reached_destructive

/--
info: 'Scidonia.RC.couple_does_not_give_count_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms couple_does_not_give_count_one

/--
info: 'Scidonia.RC.bindVar_breaks_inj' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bindVar_breaks_inj

/--
info: 'ScidoniaTest.Correspondence.prologueAcct_refInj' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms prologueAcct_refInj

/--
info: 'ScidoniaTest.Correspondence.bridge_at_actual' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bridge_at_actual

/-! The remaining new theorems' lists -/

#print axioms count_expand
#print axioms countName_cons
#print axioms countName_pos
#print axioms countName_one_pair
#print axioms countName_eq_count_fst
#print axioms count_expand_one
#print axioms pairsOf_bound
#print axioms Typed.store_count
#print axioms owns_of_correspondence
#print axioms alias_typed
#print axioms alias_bound
#print axioms alias_couple
#print axioms alias_name_count
#print axioms alias_ref_count_two
#print axioms alias_not_inj
#print axioms alias_kills_bridge
#print axioms count_one_fails_without_inj
#print axioms source_readings_differ
#print axioms source_account_not_freeName
#print axioms prologue_account_freeName
#print axioms bindVal_account_not_pairsOf
#print axioms bindVal_account_not_pairsOf_any
#print axioms source_store_env_count
#print axioms sibling_positional
#print axioms runs_at_actual
#print axioms bridge_at_reachable
#print axioms reach_ref_count_one
#print axioms reached_couple
#print axioms reach_store_typed
#print axioms pairsOf_env0_refInj
#print axioms sibling_refused

end ScidoniaTest.Correspondence
