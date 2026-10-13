/-
Checks for `Scidonia.RC.Discipline`, from outside the module.

The module fixes the judgement `Runs`: the term `e` is run at the account `m`, one
clause per construct, each the premise of the target rule that construct takes
together with the account movement that rule makes. A proof development has no
pre-fix behaviour to observe, so the checks here meet the judgement from outside, on
heaps, terms and accounts a client can build. They are of eight kinds:

* **The readings and the counts, evaluated**, as `#guard`s: the term's free
  occurrences, their references, and the pairs they name, and the branch the write
  takes at the two configurations. Each guard stands beside a control of the same
  shape whose message is pinned, so a guard is shown to fire rather than to pass
  whatever it is given.
* **The reading the judgement replaces, refuted**: `dup_model_refuted` applies
  `dup_step_overtakes_own` at the term the checks write --- the account a `dup` step
  leaves holds one occurrence more than the body's own free occurrences --- beside the
  guard that evaluates the account's pairs at the same term.
* **The judgement at the disciplined configuration**, as a derivation:
  `owned_runs` meets the store's clause from outside, reading the store's occurrence,
  the distinctness of the subject's reference, the value and the rest of the term.
* **The instruction rules applied**, at a concrete step: `release_runs` is the
  judgement at the configuration `Target.TStep.dropShared` fires at, `release_step` is
  that step at the release's own heap and account, and `release_moves` is the move
  `Scidonia.RC.runs_drop` makes from the one to the other.
* **The store's two hypotheses**, applied: `store_ownership` reads `runs_store_owned`
  at the disciplined configuration, and `store_count_one` is the distinctness conjunct
  read at the reference the environment names.
* **The composition at the root**: `composed_keeps` is `rooted_store_destructive` at
  the coupled, rooted configuration, and `composed_keeps_ownership` reaches the same
  conclusion through the store theorem the composition reads, with the judgement's
  pieces read out one by one.
* **The four goals the target's congruence and match rules do not meet**, as
  counterexamples: a judged configuration, a step of the relation at it, and a
  conclusion that is not judged. Each names the account and the environment the step
  starts from and leaves --- `appFun_account_shared` (the two positions' requirements
  resting on one occurrence), `appArg_value_not_reached` and `bindRhs_value_not_reached`
  (a position stepping into a value, whose clause carries the continuation the
  computation-shaped clause did not), and `matchC_arm_not_paired` (the arm's binders
  reading the cell's slots, which the account does not pair with them).
* **Axioms**: each representative theorem's `#print axioms` output is pinned, so a
  proof that acquires an axiom it should not fails the build rather than printing a
  longer list for a reader to notice.

The heaps below are read as exactly the cells they list, which is the reading `Counted`
is stated under; nothing here constructs a heap from a compiled run.
-/
import Scidonia.RC
import Scidonia.RC.Discipline

open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap
open Scidonia.RC

namespace ScidoniaTest.Discipline

set_option synthInstance.maxSize 400

/-! ## The heaps, the terms and the accounts the checks are read at -/

/-- The heap the disciplined write is read at: the subject's cell at `0`, whose slots
name `1` and `2`, carries the one occurrence the account holds of the subject, and the
value's cell at `2` carries the occurrence the account holds of the value. -/
def owned : CHeap :=
  [(0, { slots := [1, 2], count := 1 }), (1, { slots := [], count := 1 }),
    (2, { slots := [], count := 2 })]

/-- The same heap with the subject's cell at one occurrence more: the reading a term
that duplicates the subject's name leaves, and the heap the release below is read
at. -/
def borrowed : CHeap :=
  [(0, { slots := [1, 2], count := 2 }), (1, { slots := [], count := 1 }),
    (2, { slots := [], count := 2 })]

/-- The environment the checks read: the variable `0` names the subject's cell, and `1`
and `2` the cells of the same name. -/
def env0 : TEnv := [(0, 0), (1, 1), (2, 2)]

/-- The account at the disciplined write: one occurrence of the subject and one of the
value. -/
def acct : Multi := [(0, 0), (2, 2)]

/-- The account with the subject held twice: the reading the account has once the
subject's name is duplicated. -/
def borrowedAcct : Multi := [(0, 0), (0, 0), (2, 2)]

/-- The write the checks read: slot `0` of the cell the subject names is set to the
reference the variable `2` names. -/
def storeTerm : Expr := .store (.var 0) 0 (.var 2)

/-- The same write behind the release of the subject's occurrence. -/
def dropStoreTerm : Expr := .drop 0 storeTerm

/-- The same write behind the duplication of the subject's occurrence. -/
def dupStoreTerm : Expr := .dup 0 storeTerm

/-! ## The readings, the counts and the branch, evaluated -/

/-
The term's free occurrences, their references, and the pairs they name: the write has
the subject's occurrence and the value's, and the environment reads them at the cells
of the same name.
-/
#guard decide (uses storeTerm = [0, 2])
#guard decide (refsOf env0 (uses storeTerm) = [0, 2])
#guard decide (occsOf env0 storeTerm = [(0, 0), (2, 2)])

/--
error: Expression
  decide (uses storeTerm = [0, 0, 2])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (uses storeTerm = [0, 0, 2])

/--
error: Expression
  decide (occsOf env0 storeTerm = [(0, 0), (0, 0), (2, 2)])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (occsOf env0 storeTerm = [(0, 0), (0, 0), (2, 2)])

/-
The account of the term behind a release of the subject's occurrence, and behind its
duplication: the release's own occurrence is counted as well, and so is the
duplication's, which is what the two instructions contribute to the term's own
references.
-/
#guard decide (uses dropStoreTerm = [0, 0, 2])
#guard decide (occsOf env0 dropStoreTerm = [(0, 0), (0, 0), (2, 2)])
#guard decide (uses dupStoreTerm = [0, 0, 2])
#guard decide (occsOf env0 dupStoreTerm = [(0, 0), (0, 0), (2, 2)])

/--
error: Expression
  decide (occsOf env0 dupStoreTerm = [(0, 0), (2, 2)])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (occsOf env0 dupStoreTerm = [(0, 0), (2, 2)])

/-
The account's references at the two configurations the checks pair: the subject's cell
is named once by the disciplined account and twice in the duplicated reading, while
the value's cell is named once by both.
-/
#guard decide ((expand acct).count 0 = 1 && (expand acct).count 2 = 1)
#guard decide ((expand borrowedAcct).count 0 = 2 && (expand borrowedAcct).count 2 = 1)

/--
error: Expression
  decide (List.count 0 (expand acct) = 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((expand acct).count 0 = 2)

/-
The branch the write takes is the heap's own count at the subject's cell: one at the
disciplined configuration and two at the borrowed one.
-/
#guard decide (CHeap.count owned 0 = 1 && CHeap.count borrowed 0 = 2)

/--
error: Expression
  decide (owned.count 0 = 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (CHeap.count owned 0 = 2)

/-
The branch the write takes at the two configurations, evaluated: the disciplined write
keeps the cell's location and holds the written slots there, and the borrowed one
lands them at the heap's fresh location.
-/
#guard decide ((update owned ([] ++ expand acct) 0 [2, 2]).1.lookup 0 = some [2, 2])
#guard decide ((update borrowed ([] ++ expand borrowedAcct) 0 [2, 2]).1.lookup
  (fresh borrowed [2, 2]) = some [2, 2])

/--
error: Expression
  decide ((update owned ([] ++ expand acct) 0 [2, 2]).fst.lookup 0 = some [1, 2])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((update owned ([] ++ expand acct) 0 [2, 2]).1.lookup 0 = some [1, 2])

/-
The release's step at the borrowed configuration: the cell's count falls by one, which
is the heap the disciplined write is read at, and the account the release leaves is the
disciplined account.
-/
#guard decide ((decRef borrowed [] 0).1 = owned)
#guard decide (Multi.dropOcc borrowedAcct 0 0 = acct)

/--
error: Expression
  decide ((decRef borrowed [] 0).fst = borrowed)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((decRef borrowed [] 0).1 = borrowed)

/-! ## The reading the judgement replaces, refuted -/

/-- The account a `dup` step leaves is one occurrence above the body's own free
occurrences, and the body's own account is the body of the rule's account: the
instruction's own occurrence is still on it, because `uses` counts the instruction's
name besides its body's occurrences. An account that *is* the term's free occurrences
read through the environment therefore cannot survive the instruction, which is why the
judgement of `Scidonia.RC.Discipline` is a clause-per-construct relation and not that
identity. -/
theorem dup_model_refuted :
    Multi.dropOcc (Multi.insert (occsOf env0 dupStoreTerm) 0 0) 0 0 = occsOf env0 dupStoreTerm
      ∧ Multi.insert (occsOf env0 dupStoreTerm) 0 0 ≠ occsOf env0 storeTerm :=
  dup_step_overtakes_own (by decide)

/-- The refutation's first conjunct at the term the checks write: the body's own
account is the rule's account with the supplied occurrence removed. -/
theorem dup_model_body :
    Multi.dropOcc (Multi.insert (occsOf env0 dupStoreTerm) 0 0) 0 0
      = occsOf env0 dupStoreTerm :=
  dup_model_refuted.1

/-- The refutation's second conjunct at the term the checks write: the account the rule
leaves is not the body's own free occurrences. -/
theorem dup_model_not_own :
    Multi.insert (occsOf env0 dupStoreTerm) 0 0 ≠ occsOf env0 storeTerm :=
  dup_model_refuted.2

/-! ## The judgement at the disciplined configuration -/

/-- The judgement holds at the disciplined configuration: the write's clause is met
from outside --- the account holds the store's occurrence, the environment's reference
for the subject is counted once, and the value and the rest of the term run. -/
theorem owned_runs : Runs env0 acct storeTerm := by
  change Runs env0 acct (.store (.var 0) 0 (.var 2))
  refine Runs.store (ρ := env0) (y := 0) (i := 0) (v := .var 2) (m := acct)
    (Owns.store (m := acct) (y := 0) (r := 0) (i := 0) (v := .var 2)
      (by decide) (by decide)) ?_ ?_ ?_
  · intro r hr
    have hr0 : r = 0 :=
      Option.some.inj (hr.symm.trans (by decide : env0.lookup 0 = some (0 : Ref)))
    rw [hr0]
    decide
  · exact Runs.var (ρ := env0) (x := 2) (r := 2) (m := acct) (by decide) (by decide)
  · exact Runs.var (ρ := env0) (x := 0) (r := 0) (m := acct) (by decide) (by decide)

/-- The judgement at the write the checks read at the account the release leaves: the
same derivation, the release's account being the disciplined one. -/
theorem acct_runs : Runs env0 (Multi.dropOcc borrowedAcct 0 0) storeTerm :=
  owned_runs

/-- The subject's occurrence is one the account holds, and the environment's reading of
it is counted once: the store's two hypotheses read off the judgement by
`Scidonia.RC.runs_store_owned`. -/
theorem store_ownership : Owns env0 acct storeTerm
    ∧ ∃ r, env0.lookup 0 = some r ∧ (expand acct).count r = 1 :=
  runs_store_owned owned_runs

/-- The write's ownership, read as the pair the account holds. -/
theorem store_owns_holds : Owns env0 acct storeTerm := store_ownership.1

/-- The account counts the subject's reference once: the distinctness conjunct the
store's clause carries, read at the reference the environment names. -/
theorem store_count_one : (expand acct).count 0 = 1 := by
  obtain ⟨_, r, hr, hcount⟩ := store_ownership
  have h0 : env0.lookup 0 = some (0 : Ref) := by decide
  have hrr : r = 0 := Option.some.inj (hr.symm.trans h0)
  rw [← hrr]
  exact hcount

/-! ## The instruction rules applied at a concrete step -/

/-- The judgement at the configuration the release fires at: the release's clause, with
the continuation read at the account the release leaves. -/
theorem release_runs : Runs env0 borrowedAcct dropStoreTerm :=
  Runs.drop (hρ := by decide) (hmem := by decide) (h := acct_runs)

/-- The release's step at the release's own heap: the account the step leaves is the
one the judgement is preserved to. -/
theorem release_step : TStep borrowed [] env0 borrowedAcct dropStoreTerm
    (decRef borrowed [] 0).1 [] env0 (Multi.dropOcc borrowedAcct 0 0) storeTerm :=
  TStep.dropShared (hρ := by decide) (h2 := by decide) (hsub := by decide)

/-- The release's move with the judgement standing at both ends: the move
`Scidonia.RC.runs_drop` makes at the release's own premises is the move the
configuration's step makes, and the account the release leaves holds the write's
clause. -/
theorem release_moves : Runs env0 (Multi.dropOcc borrowedAcct 0 0) storeTerm :=
  runs_drop (by decide) (by decide) release_runs

/-! ## The composition at the root -/

/-- The disciplined configuration's heap is well formed. -/
theorem owned_wf : CHeap.WF owned := by rw [CHeap.WF]; decide

/-- A heap is counted when every cell it lists carries the count its occurrences and
its hands give it, every slot names a cell it lists, and every reference the account
holds names one. These are the three conditions a reader can check at a small
heap. -/
theorem counted_of (c : CHeap) (hs : List Ref)
    (hcount : ∀ x ∈ CHeap.refs c, CHeap.count c x = (CHeap.slots c).count x + hs.count x)
    (hslot : ∀ x ∈ CHeap.slots c, x ∈ CHeap.refs c)
    (hhandle : ∀ x ∈ hs, x ∈ CHeap.refs c) : Counted c hs := by
  rw [counted_iff_slots]
  intro x
  by_cases hx : x ∈ CHeap.refs c
  · exact hcount x hx
  · have hs0 : (CHeap.slots c).count x = 0 :=
      List.count_eq_zero.mpr (fun hmem => hx (hslot x hmem))
    have hh0 : hs.count x = 0 :=
      List.count_eq_zero.mpr (fun hmem => hx (hhandle x hmem))
    rw [CHeap.count_eq_zero_of_not_mem hx, hs0, hh0]

/-- The disciplined configuration's heap is counted at the account's own
references. -/
theorem owned_counted : Counted owned ([] ++ expand acct) := by
  refine counted_of owned ([] ++ expand acct) ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by simpa [owned] using hx
    rcases hx' with rfl | rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 1 ∨ x = 2 := by simpa [owned] using hx
    rcases hx' with rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 0 ∨ x = 2 := by simpa [acct] using hx
    rcases hx' with rfl | rfl <;> decide

/-- The account's pairs name the reference the environment binds their variable to. -/
theorem acct_bound : Bound env0 acct := by
  intro p hp
  have hp' : p = (0, 0) ∨ p = (2, 2) := by simpa [acct] using hp
  rcases hp' with rfl | rfl <;> decide

/-- The disciplined configuration satisfies the coupling invariant. -/
theorem owned_couple : Couple owned [] env0 acct :=
  ⟨owned_wf, owned_counted, acct_bound⟩

/-- The root's shape at the disciplined configuration: no slot and no handle names the
subject's cell. -/
theorem owned_rooted : Rooted owned [] 0 := by
  constructor <;> decide

/-- The composition at the root: the disciplined write at the root of the coupled
configuration keeps the cell's location, and the judgement is what supplies the two
premises the store theorem cannot derive. -/
theorem composed_keeps :
    (update owned ([] ++ expand acct) 0 [2, 2]).1.lookup 0 = some [2, 2] :=
  rooted_store_destructive owned_couple (by decide) owned_runs owned_rooted (by decide)

/-- The same conclusion through the store theorem the composition reads, with the
judgement's pieces read out one by one. -/
theorem composed_keeps_ownership :
    (update owned ([] ++ expand acct) 0 [2, 2]).1.lookup 0 = some [2, 2] := by
  obtain ⟨hown, r, hr, hcount⟩ := store_ownership
  have h0 : env0.lookup 0 = some (0 : Ref) := by decide
  have hrr : r = 0 := (Option.some.inj (by rw [h0] at hr; exact hr)).symm
  exact store_owned_is_destructive owned_couple (by decide) hown (by rw [← hrr]; exact hcount)
    (by decide) (by decide) (by decide)

/-! ## The four goals the target's congruence and match rules do not meet

Each check is a judged configuration, a step of the relation at it, and a conclusion
that is not judged. The account of a configuration whose two positions both rest on one
occurrence is the judgement's own: its clauses are the rules' premises, and the rules'
premises are membership in the configuration's account. -/

/-- The heap the two-position checks step at: the account's cell at `2` and the check's
cell at `3`, each carrying two occurrences. -/
def shared : CHeap :=
  [(2, { slots := [], count := 2 }), (3, { slots := [], count := 2 })]

/-- The environment the two-position checks read. -/
def env1 : TEnv := [(2, 2), (3, 3)]

/-- The account of the `appFun` check: one pair, which both positions' clauses are met
by. -/
def onePair : Multi := [(2, 2)]

/-- The account of the `bindRhs` and `appArg` checks: the check's cell's pair and the
account's. -/
def twoPairs : Multi := [(2, 2), (3, 3)]

/-- The environment the two-position checks read binds `2` at the reference `2`. -/
theorem env1_two : env1.lookup 2 = some (2 : Ref) := by decide

/-- A hypothesis that binds `2` in the environment the two-position checks read names
the reference `2`. -/
theorem env1_two_unique {r : Ref} (h : env1.lookup 2 = some r) : r = 2 :=
  Option.some.inj (h.symm.trans env1_two)

/-- The environment a binding of `0` leaves binds `2` at the reference `2`. -/
theorem set_env1_two (r' : Ref) : (TEnv.set env1 0 r').lookup 2 = some (2 : Ref) := by
  rw [TEnv.lookup_set_of_ne (show (0 : Var) ≠ 2 by decide) r']
  exact env1_two

/-- A hypothesis that binds `2` after a binding of `0` names the reference `2`. -/
theorem set_env1_two_unique {r r' : Ref}
    (h : (TEnv.set env1 0 r').lookup 2 = some r) : r = 2 :=
  Option.some.inj (h.symm.trans (set_env1_two r'))

/-- The function position of the `appFun` check runs: the release's clause, with the
continuation read at the account the release leaves. -/
theorem appFun_function_runs : Runs env1 onePair (.drop 2 (.con0 0)) :=
  Runs.drop (hρ := env1_two) (hmem := by decide)
    (h := Runs.con0 (ρ := env1) 0 (Multi.dropOcc onePair 2 2))

/-- The argument of the `appFun` check runs: the variable's clause, met by the same
pair the release's clause is met by. -/
theorem appFun_argument_runs : Runs env1 onePair (.var 2) :=
  Runs.var (ρ := env1) (x := 2) (r := 2) (m := onePair) (by decide) (by decide)

/-- The `appFun` check's configuration is judged: its function position is a
computation, which is what `Runs.appPos` asks of an application, and both positions'
clauses are met by the account's one pair. -/
theorem appFun_judged : Runs env1 onePair (.app (.drop 2 (.con0 0)) (.var 2)) :=
  Runs.appPos (hval := by intro hval; cases hval) (hf := appFun_function_runs)
    (ha := appFun_argument_runs)

/-- The `appFun` check's configuration is not judged once its function position has
stepped: its function is a nullary node, whose clause is not a position's step, and its
argument's clause has no pair to rest on. -/
theorem appFun_not_judged : ¬ Runs env1 (Multi.dropOcc onePair 2 2)
    (.app (.con0 0) (.var 2)) := by
  intro h
  cases h with
  | appPos hval _ _ => exact absurd (Value.con0 0) hval
  | appArgPos _ _ ha =>
      cases ha with
      | var hρ hmem =>
          rw [env1_two_unique hρ] at hmem
          exact absurd hmem (by simp [onePair, Multi.dropOcc])

/-- The `appFun` check's step: the function position releases the occurrence the
argument's clause rests on. -/
theorem appFun_step : TStep shared [] env1 onePair (.app (.drop 2 (.con0 0)) (.var 2))
    (decRef shared [] 2).1 [] env1 (Multi.dropOcc onePair 2 2) (.app (.con0 0) (.var 2)) :=
  TStep.appFun (TStep.dropShared (hρ := env1_two) (h2 := by decide) (hsub := by decide))

/-- The `appFun` goal, refused: judged, stepped, and not judged at the step's
conclusion. The account is the one the judgement admits --- two positions' clauses met
by one pair --- which is why the goal is unprovable and not merely unproved. -/
theorem appFun_account_shared :
    Runs env1 onePair (.app (.drop 2 (.con0 0)) (.var 2))
      ∧ TStep shared [] env1 onePair (.app (.drop 2 (.con0 0)) (.var 2))
          (decRef shared [] 2).1 [] env1 (Multi.dropOcc onePair 2 2) (.app (.con0 0) (.var 2))
      ∧ ¬ Runs env1 (Multi.dropOcc onePair 2 2) (.app (.con0 0) (.var 2)) :=
  ⟨appFun_judged, appFun_step, appFun_not_judged⟩

/-- The `bindRhs` check's configuration is judged: its bound term is a computation,
and the release and the body both run at the account. -/
theorem bindRhs_judged : Runs env1 twoPairs (.bind 0 (.drop 3 (.var 2)) (.var 2)) :=
  Runs.bindPos (hval := by intro hval; cases hval)
    (h₁ := Runs.drop (hρ := by decide) (hmem := by decide)
      (h := Runs.var (ρ := env1) (x := 2) (r := 2) (m := Multi.dropOcc twoPairs 3 3)
        (by decide) (by decide)))
    (h₂ := Runs.var (ρ := env1) (x := 2) (r := 2) (m := twoPairs) (by decide) (by decide))

/-- The `bindRhs` check's configuration is not judged once its bound term has stepped
into the variable the write runs on: the clause for a binding whose bound term is a
variable asks for the body's own judgement at the account the binding leaves, and the
body's occurrence of the subject is not one that account holds. -/
theorem bindRhs_not_judged : ¬ Runs env1 (Multi.dropOcc twoPairs 3 3)
    (.bind 0 (.var 2) (.var 2)) := by
  intro h
  cases h with
  | bindVar hρ _ _ hcont =>
      rw [env1_two_unique hρ] at hcont
      cases hcont with
      | var hρ' hmem =>
          rw [set_env1_two_unique hρ'] at hmem
          exact absurd hmem (by simp [twoPairs, Multi.insert, Multi.dropOcc])
  | bindVal hnovar _ _ _ => exact absurd rfl (hnovar 2)
  | bindPos hval _ _ => exact absurd (Value.var 2) hval

/-- The `bindRhs` check's step: the bound term releases the check's cell's occurrence
and becomes the variable the write runs on. -/
theorem bindRhs_step : TStep shared [] env1 twoPairs (.bind 0 (.drop 3 (.var 2)) (.var 2))
    (decRef shared [] 3).1 [] env1 (Multi.dropOcc twoPairs 3 3) (.bind 0 (.var 2) (.var 2)) :=
  TStep.bindRhs (TStep.dropShared (hρ := by decide) (h2 := by decide) (hsub := by decide))

/-- The `bindRhs` goal, refused: judged, stepped, and not judged at the step's
conclusion. -/
theorem bindRhs_value_not_reached :
    Runs env1 twoPairs (.bind 0 (.drop 3 (.var 2)) (.var 2))
      ∧ TStep shared [] env1 twoPairs (.bind 0 (.drop 3 (.var 2)) (.var 2))
          (decRef shared [] 3).1 [] env1 (Multi.dropOcc twoPairs 3 3)
          (.bind 0 (.var 2) (.var 2))
      ∧ ¬ Runs env1 (Multi.dropOcc twoPairs 3 3) (.bind 0 (.var 2) (.var 2)) :=
  ⟨bindRhs_judged, bindRhs_step, bindRhs_not_judged⟩

/-- The `appArg` check's configuration is judged: its function is an abstraction and
its argument is a computation, and the argument runs at the account. -/
theorem appArg_judged :
    Runs env1 twoPairs (.app (.lam 0 (.var 1)) (.drop 3 (.var 2))) :=
  Runs.appLamArg (hval := by intro hval; cases hval)
    (ha := Runs.drop (hρ := by decide) (hmem := by decide)
      (h := Runs.var (ρ := env1) (x := 2) (r := 2) (m := Multi.dropOcc twoPairs 3 3)
        (by decide) (by decide)))

/-- The `appArg` check's configuration is not judged once its argument has stepped
into a variable: the clause for an abstraction applied to a variable asks for the
body's own judgement at the parameter's binding, and the body's variable is read
nowhere by the environment. -/
theorem appArg_not_judged : ¬ Runs env1 (Multi.dropOcc twoPairs 3 3)
    (.app (.lam 0 (.var 1)) (.var 2)) := by
  intro h
  cases h with
  | appVar hρ _ _ hcont =>
      rw [env1_two_unique hρ] at hcont
      cases hcont with
      | var hρ' _ =>
          have hnone : (TEnv.set env1 0 2).lookup 1 = none := by decide
          rw [hnone] at hρ'
          cases hρ'
  | appVal hnovar _ _ _ => exact absurd rfl (hnovar 2)
  | appPos hval _ _ => exact absurd (Value.lam 0 (.var 1)) hval
  | appArgPos _ hnotlam _ => exact absurd rfl (hnotlam 0 (.var 1))
  | appLamArg hval _ => exact absurd (Value.var 2) hval

/-- The `appArg` check's step: the argument releases the check's cell's occurrence and
becomes a variable. -/
theorem appArg_step : TStep shared [] env1 twoPairs
    (.app (.lam 0 (.var 1)) (.drop 3 (.var 2)))
    (decRef shared [] 3).1 [] env1 (Multi.dropOcc twoPairs 3 3)
    (.app (.lam 0 (.var 1)) (.var 2)) :=
  TStep.appArg (Value.lam 0 (.var 1))
    (TStep.dropShared (hρ := by decide) (h2 := by decide) (hsub := by decide))

/-- The `appArg` goal, refused: judged, stepped, and not judged at the step's
conclusion. -/
theorem appArg_value_not_reached :
    Runs env1 twoPairs (.app (.lam 0 (.var 1)) (.drop 3 (.var 2)))
      ∧ TStep shared [] env1 twoPairs (.app (.lam 0 (.var 1)) (.drop 3 (.var 2)))
          (decRef shared [] 3).1 [] env1 (Multi.dropOcc twoPairs 3 3)
          (.app (.lam 0 (.var 1)) (.var 2))
      ∧ ¬ Runs env1 (Multi.dropOcc twoPairs 3 3) (.app (.lam 0 (.var 1)) (.var 2)) :=
  ⟨appArg_judged, appArg_step, appArg_not_judged⟩

/-! ## The non-lambda `appArg` failure, inherited from the nested `appFun`

`Runs.appArgPos` --- the clause for an application whose function is a value that is not
an abstraction --- reads the argument and nothing else, so it preserves whenever the
argument position does. A counterexample at a *top-level* `appArg` with a non-lambda
function therefore has to be one whose *argument* is already such a configuration: the
wrapper below is the `appFun` check as the argument of an application whose function is
a nullary node, and its failure is the argument's, not the application's own clause. -/

/-- The `appFun` check wrapped as the argument of an application whose function is a
value that is not an abstraction. -/
theorem appArg_inherited_judged :
    Runs env1 onePair (.app (.con0 5) (.app (.drop 2 (.con0 0)) (.var 2))) :=
  Runs.appArgPos (Value.con0 5) (by intro x body h; cases h) appFun_judged

/-- The wrapper's step: the argument's own step, taken by the application's `appArg`
rule. -/
theorem appArg_inherited_step :
    TStep shared [] env1 onePair (.app (.con0 5) (.app (.drop 2 (.con0 0)) (.var 2)))
      (decRef shared [] 2).1 [] env1 (Multi.dropOcc onePair 2 2)
      (.app (.con0 5) (.app (.con0 0) (.var 2))) :=
  TStep.appArg (Value.con0 5) appFun_step

/-- The wrapper is not judged once its argument has stepped: the failure is the
argument's, and the application's own clause is the one that carried it. -/
theorem appArg_inherited_not_judged :
    ¬ Runs env1 (Multi.dropOcc onePair 2 2) (.app (.con0 5) (.app (.con0 0) (.var 2))) := by
  intro h
  cases h with
  | appArgPos _ _ ha => exact appFun_not_judged ha
  | appPos hne _ _ => exact absurd (Value.con0 5) hne

/-- The nested-wrapper goal, refused: a configuration judged and stepped, whose
conclusion is not judged because the *argument* is not --- the failure is inherited from
`appFun` and not a sibling-resource overlap of the application's own clause, which reads
only the argument. -/
theorem appArg_nested_inherited :
    Runs env1 onePair (.app (.con0 5) (.app (.drop 2 (.con0 0)) (.var 2)))
      ∧ TStep shared [] env1 onePair (.app (.con0 5) (.app (.drop 2 (.con0 0)) (.var 2)))
          (decRef shared [] 2).1 [] env1 (Multi.dropOcc onePair 2 2)
          (.app (.con0 5) (.app (.con0 0) (.var 2)))
      ∧ ¬ Runs env1 (Multi.dropOcc onePair 2 2)
          (.app (.con0 5) (.app (.con0 0) (.var 2))) :=
  ⟨appArg_inherited_judged, appArg_inherited_step, appArg_inherited_not_judged⟩

/-! ## The value clause, narrower than the rule it mirrors

`Runs.bindVal` asks the resumed body to be judged at *every* reference the binder could
take, while the target's `bindVal` resumes at the one reference its `ValRef` returns. At
the configuration below the binding is not judged, because the body's write is
undisciplined at `r = 0`, where the account holds three occurrences of the subject; the
target nonetheless reaches a disciplined state from it, because `bindVal` realises the
value at the heap's fresh location and the body is judged there. The universally
quantified obligation is what the judgement adds beyond the rule. -/

/-- The environment of the value-clause check: `1` and `2` both name the reference `0`. -/
def envR : TEnv := [(1, 0), (2, 0)]

/-- The account of the value-clause check: one occurrence of each of `1` and `2`. -/
def mR : Multi := [(1, 0), (2, 0)]

/-- The body of the value-clause check: a write to `0` at the value `1`. The subject `0`
is the binder's, so it is the one occurrence the binder supplies. -/
def bindBody : Expr := .store (.var 0) 0 (.var 1)

/-- The binding the value-clause check reads: `con0 7` bound to `0`. -/
def bindTerm : Expr := .bind 0 (.con0 7) bindBody

/-- The body is judged once the binder's reference is not `0`: the write's subject is
counted once there. -/
theorem bindBody_runs_of_ne {r₀ : Ref} (hr : r₀ ≠ 0) :
    Runs (TEnv.set envR 0 r₀) (Multi.insert mR 0 r₀) bindBody := by
  refine Runs.store (ρ := TEnv.set envR 0 r₀) (y := 0) (i := 0) (v := .var 1)
    (m := Multi.insert mR 0 r₀)
    (Owns.store (m := Multi.insert mR 0 r₀) (y := 0) (r := r₀) (i := 0) (v := .var 1)
      (hρ := TEnv.lookup_set_self envR 0 r₀) (hmem := by simp [Multi.insert])) ?_ ?_ ?_
  · intro r' hr'
    have hrr : r' = r₀ :=
      Option.some.inj (hr'.symm.trans (TEnv.lookup_set_self envR 0 r₀))
    rw [hrr]
    have hexp : expand (Multi.insert mR 0 r₀) = r₀ :: expand mR := rfl
    rw [hexp, List.count_cons_self]
    have hz : (expand mR).count r₀ = 0 := by
      rw [show expand mR = [0, 0] from rfl]
      exact List.count_eq_zero.mpr (by simp [hr])
    rw [hz]
  · refine Runs.var (x := 1) (r := 0) (hρ := ?_) (hmem := ?_)
    · rw [TEnv.lookup_set_of_ne (show (0 : Var) ≠ 1 by decide) r₀]
      decide
    · exact List.mem_cons_of_mem _ (by decide)
  · exact Runs.var (x := 0) (r := r₀) (hρ := TEnv.lookup_set_self envR 0 r₀)
      (hmem := by simp [Multi.insert])

/-- The binding is not judged: `Runs.bindVal` demands the body judge for every reference
`r`, and at `r = 0` the body's write is undisciplined. -/
theorem bindVal_not_judged : ¬ Runs envR mR bindTerm := by
  intro h
  unfold bindTerm at h
  cases h with
  | bindVal _ _ _ hcont =>
      have hb0 : ¬ Runs (TEnv.set envR 0 0) (Multi.insert mR 0 0) bindBody := by
        intro hb
        unfold bindBody at hb
        cases hb with
        | store _ hdist =>
            have hlook : (TEnv.set envR 0 0).lookup 0 = some (0 : Ref) := by decide
            exact absurd (hdist 0 hlook) (by decide)
      exact hb0 (hcont 0)
  | bindPos hval _ _ => exact absurd (Value.con0 7) hval

/-- The body is judged at the reference `1`, which is not `0`. -/
theorem bindVal_body_judged : Runs (TEnv.set envR 0 1) (Multi.insert mR 0 1) bindBody :=
  bindBody_runs_of_ne (by decide)

/-- The target reaches the disciplined state: the binding's `bindVal` step realises the
value at the heap's fresh location and resumes the body, which is judged there. -/
theorem bindVal_step :
    TStep [] [] envR mR bindTerm (allocWith [] [] []).1
      (dropHandle (allocWith [] [] []).2 (fresh [] []))
      (TEnv.set envR 0 (fresh [] [])) (Multi.insert mR 0 (fresh [] [])) bindBody :=
  TStep.bindVal (ValRef.con0) (by intro z h; cases h) (by decide)

/-- The binding's step reaches a configuration whose body is judged: the judgement
excludes the binding, and the rule's own realisation reaches a state the judgement
accepts. -/
theorem bindVal_step_reaches :
    ∃ c' hs' r, r ≠ 0
      ∧ TStep [] [] envR mR bindTerm c' hs' (TEnv.set envR 0 r) (Multi.insert mR 0 r) bindBody
      ∧ Runs (TEnv.set envR 0 r) (Multi.insert mR 0 r) bindBody :=
  ⟨(allocWith [] [] []).1, dropHandle (allocWith [] [] []).2 (fresh [] []), fresh [] [],
    by decide, bindVal_step, bindBody_runs_of_ne (by decide)⟩

/-- The heap the match check steps at: the cell the subject names at `5`, whose one
slot names `7`. -/
def matched : CHeap :=
  [(5, { slots := [7], count := 1 }), (7, { slots := [], count := 1 })]

/-- The environment the match check reads. -/
def env2 : TEnv := [(5, 5)]

/-- The account the match check is read at: the subject's occurrence. -/
def matchAcct : Multi := [(5, 5)]

/-- The match check's configuration is judged: the subject's occurrence is held, and
the arm's body runs at the binding the account pairs with the binder. The demand is
vacuous at the account the rule fires at, whose pairs name none of the arm's
binders. -/
theorem match_judged : Runs env2 matchAcct (.matchC (.var 5) 0 [6] (.var 6)) := by
  refine Runs.matchC (ρ := env2) (z := 5) (r := 5) (c := 0) (ys := [6]) (body := .var 6)
    (m := matchAcct) (by decide) (by decide) ?_
  intro rs hlen hpair
  cases rs with
  | nil => simp at hlen
  | cons r rs' =>
      cases rs' with
      | nil => exact absurd (hpair (6, r) (by simp)) (by simp [matchAcct])
      | cons r2 rs'' => simp at hlen

/-- The match check's step: the arm's binder receives the slot the cell holds. -/
theorem match_step : TStep matched [] env2 matchAcct (.matchC (.var 5) 0 [6] (.var 6))
    matched [] (TEnv.bindAll env2 [6] [7]) matchAcct (.var 6) :=
  TStep.matchC (c := matched) (hs := []) (ρ := env2) (m := matchAcct) (z := 5) (ctag := 0)
    (ys := [6]) (body := .var 6) (r := 5) (by decide) (by decide) (by decide)

/-- The configuration the match step leaves is not judged: the arm's body reads the
binder the rule bound to the cell's slot `7`, and the account pairs the binder with no
reference. -/
theorem match_not_judged : ¬ Runs (TEnv.bindAll env2 [6] [7]) matchAcct (.var 6) := by
  intro h
  cases h with
  | var hρ hmem =>
      have h7 : (TEnv.bindAll env2 [6] [7]).lookup 6 = some (7 : Ref) := by decide
      have hr : _ = 7 := Option.some.inj (hρ.symm.trans h7)
      rw [hr] at hmem
      exact absurd hmem (by simp [matchAcct])

/-- The `matchC` goal, refused: judged, stepped, and not judged at the step's
conclusion. The rule reads the arm's binders out of the cell's slots and leaves the
account unchanged, and its premise that the binders shadow none of the account's names
is what makes the clause's demand vacuous at the configurations it fires at. -/
theorem matchC_arm_not_paired :
    Runs env2 matchAcct (.matchC (.var 5) 0 [6] (.var 6))
      ∧ TStep matched [] env2 matchAcct (.matchC (.var 5) 0 [6] (.var 6))
          matched [] (TEnv.bindAll env2 [6] [7]) matchAcct (.var 6)
      ∧ ¬ Runs (TEnv.bindAll env2 [6] [7]) matchAcct (.var 6) :=
  ⟨match_judged, match_step, match_not_judged⟩

/-! ## Axioms of representative theorems -/

/--
info: 'Scidonia.RC.dup_step_overtakes_own' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dup_step_overtakes_own

/--
info: 'Scidonia.RC.runs_dup' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms runs_dup

/--
info: 'Scidonia.RC.runs_store_owned' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms runs_store_owned

/--
info: 'Scidonia.RC.value_does_not_step' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms value_does_not_step

/--
info: 'Scidonia.RC.rooted_store_destructive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rooted_store_destructive

/--
info: 'ScidoniaTest.Discipline.owned_runs' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms owned_runs

/--
info: 'ScidoniaTest.Discipline.composed_keeps' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms composed_keeps

/--
info: 'ScidoniaTest.Discipline.appArg_value_not_reached' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms appArg_value_not_reached

/--
info: 'Scidonia.RC.runs_drop' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms runs_drop

/--
info: 'Scidonia.RC.runs_bindVar' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms runs_bindVar

/--
info: 'Scidonia.RC.runs_bindVal' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms runs_bindVal

/--
info: 'Scidonia.RC.runs_appVar' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms runs_appVar

/--
info: 'Scidonia.RC.runs_appVal' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms runs_appVal

/--
info: 'Scidonia.RC.runs_storeShared' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms runs_storeShared

/--
info: 'Scidonia.RC.runs_con2FieldL' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms runs_con2FieldL

/--
info: 'ScidoniaTest.Discipline.dup_model_refuted' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dup_model_refuted

/--
info: 'ScidoniaTest.Discipline.appFun_account_shared' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms appFun_account_shared

/--
info: 'ScidoniaTest.Discipline.bindRhs_value_not_reached' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bindRhs_value_not_reached

/--
info: 'ScidoniaTest.Discipline.matchC_arm_not_paired' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms matchC_arm_not_paired

/--
info: 'ScidoniaTest.Discipline.appArg_nested_inherited' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms appArg_nested_inherited

/--
info: 'ScidoniaTest.Discipline.bindVal_not_judged' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms bindVal_not_judged

/--
info: 'ScidoniaTest.Discipline.bindVal_step_reaches' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bindVal_step_reaches

/--
info: 'Scidonia.RC.runs_appArgPos' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.runs_appArgPos

end ScidoniaTest.Discipline
