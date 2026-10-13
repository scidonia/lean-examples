/-
Checks for `Scidonia.RC.Discipline`, from outside the module.

The module fixes what a term's account is (`AccountOf`: the term's own occurrences, read
through the environment), the clause a write's subject has to satisfy (`WritesOwned`), the
condition under which "once in the term" means "once in the account" (`InjectiveOn`), and
the three together as `WellFormed`. A proof development has no pre-fix behaviour to
observe, so the checks here meet those definitions and theorems from outside, on heaps,
terms and multiplicities a client can build. They are of eight kinds:

* **The readings and the counts, evaluated**, as `#guard`s: the term's free occurrences,
  their references, and the pairs they name, at the term the checks write and at the term
  behind the duplication of the subject's name; and the branch the write takes at the two
  configurations. Each guard stands beside a control of the same shape whose message is
  pinned, so a guard is shown to fire rather than to pass whatever it is given.
* **The discipline's own clause, refused**, as theorems: a write whose subject's name occurs
  twice among the term's free occurrences, and one whose subject is not a variable, are not
  `WritesOwned`, each beside the affirmative control at the same shape --- the write whose
  subject occurs once, which is.
* **The borrowed countermodel and its affirmative counterpart**, as theorems about concrete
  configurations of one term: with the subject's occurrence held once the configuration is
  `WellFormed` and the write keeps its cell's location, and with the subject held twice ---
  the reading a term that duplicates the subject's name leaves --- the configuration is not
  `WellFormed` and the write copies. The two configurations are one term on heaps of one
  shape whose subject's cell carries the two counts, which is what the discipline's failure
  is about.
* **The coupling invariant at those configurations**, read from outside: the heaps are well
  formed and counted at the term's own references.
* **The three theorems applied**, at those concrete terms: the discipline's implication for
  the store's two hypotheses, the release's move with the discipline standing at both ends
  of a concrete step, and the composition at the root of the coupled configuration.
* **The moves the account does not make**, at concrete terms: the account the `dup` rule
  leaves is one occurrence above the body's own, and the store's account is not the
  result's own.
* **The store theorems of `Ownership`, applied**, so that a reader can compare the
  composition's conclusion with the pair it reads: the destructive branch at the
  disciplined configuration and the copying branch at the borrowed one.
* **Axioms**: each representative theorem's `#print axioms` output is pinned to the
  standard kernel principles, so a proof that acquires any other axiom fails the build
  rather than printing a longer list for a reader to notice.

The heaps below are read as exactly the cells they list, which is the reading `Counted` is
stated under; nothing here constructs a heap from a compiled run.
-/
import Scidonia.RC
import Scidonia.RC.Discipline

open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap
open Scidonia.RC

namespace ScidoniaTest.Discipline

set_option synthInstance.maxSize 400

/-! ## The heaps, the terms and the multiplicities the checks are read at -/

/-- The heap the disciplined write is read at: the subject's cell at `0`, whose slots name
`1` and `2`, carries the one occurrence the term's own account holds of the subject, and the
value's cell at `2` carries the occurrence the account holds of the value. -/
def owned : CHeap :=
  [(0, { slots := [1, 2], count := 1 }), (1, { slots := [], count := 1 }),
    (2, { slots := [], count := 2 })]

/-- The same heap with the subject's cell at one occurrence more: the reading a term that
duplicates the subject's name leaves, and the countermodel's heap. -/
def borrowed : CHeap :=
  [(0, { slots := [1, 2], count := 2 }), (1, { slots := [], count := 1 }),
    (2, { slots := [], count := 2 })]

/-- The environment the checks read: the variable `0` names the subject's cell, and `1` and
`2` the cells of the same name. -/
def env0 : TEnv := [(0, 0), (1, 1), (2, 2)]

/-- The term's own account at the write: one occurrence of the subject and one of the
value. -/
def acct : Multi := [(0, 0), (2, 2)]

/-- The account with the subject held twice: the reading the term's own account has once
the subject's name is duplicated. -/
def borrowedAcct : Multi := [(0, 0), (0, 0), (2, 2)]

/-- The write the checks read: slot `0` of the cell the subject names is set to the
reference the variable `2` names. -/
def storeTerm : Expr := .store (.var 0) 0 (.var 2)

/-- The same write behind the release of the subject's occurrence. -/
def dropStoreTerm : Expr := .drop 0 storeTerm

/-- The same write behind the duplication of the subject's occurrence. -/
def dupStoreTerm : Expr := .dup 0 storeTerm

/-- A write whose subject's name occurs twice among its free occurrences: the value names
the subject. -/
def twiceSubject : Expr := .store (.var 0) 0 (.var 0)

/-- A write whose subject is not a variable. -/
def notVarSubject : Expr := .store (.con0 5) 0 (.var 2)

/-! ## The readings, the counts and the branch, evaluated -/

/-
The term's free occurrences, their references, and the pairs they name: the write has the
subject's occurrence and the value's, and the environment reads them at the cells of the
same name.
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
  decide (refsOf env0 (uses storeTerm) = [0, 2, 2])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (refsOf env0 (uses storeTerm) = [0, 2, 2])

/--
error: Expression
  decide (occsOf env0 storeTerm = [(0, 0), (0, 0), (2, 2)])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (occsOf env0 storeTerm = [(0, 0), (0, 0), (2, 2)])

/-
The account of the term behind a release of the subject's occurrence, and behind its
duplication: the release's own occurrence is counted as well, and so is the duplication's,
which is what the two instructions contribute to the term's own references.
-/
#guard decide (uses dropStoreTerm = [0, 0, 2])
#guard decide (occsOf env0 dropStoreTerm = [(0, 0), (0, 0), (2, 2)])
#guard decide (uses dupStoreTerm = [0, 0, 2])
#guard decide (occsOf env0 dupStoreTerm = [(0, 0), (0, 0), (2, 2)])

/--
error: Expression
  decide (uses dropStoreTerm = [0, 2])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (uses dropStoreTerm = [0, 2])

/--
error: Expression
  decide (occsOf env0 dupStoreTerm = [(0, 0), (2, 2)])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (occsOf env0 dupStoreTerm = [(0, 0), (2, 2)])

/-
The account's references at the two configurations the countermodel pairs: the subject's
cell is named once by the term's own account and twice in the borrowed reading, while the
value's cell is named once by both.
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

/--
error: Expression
  decide (List.count 0 (expand borrowedAcct) = 1)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((expand borrowedAcct).count 0 = 1)

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
The store's branch at the two configurations, evaluated: the disciplined write keeps the
cell's location and holds the written slots there, and the borrowed one lands them at the
heap's fresh location.
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

/--
error: Expression
  decide ((update borrowed ([] ++ expand borrowedAcct) 0 [2, 2]).fst.lookup 0 = some [2, 2])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((update borrowed ([] ++ expand borrowedAcct) 0 [2, 2]).1.lookup 0
  = some [2, 2])

/-
The release's step at the borrowed configuration: the cell's count falls by one, which is
the heap the disciplined write is read at, and the multiplicity the release leaves is the
term's own account at the write.
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

/-
The release's step, run: the configuration the step relation leaves is the one the
disciplined write is read at, which is what the account's move and the heap's decrement
both say.
-/
#guard decide (trun 1 (borrowed, [], env0, borrowedAcct, dropStoreTerm)
  = (owned, [], env0, acct, storeTerm))

/--
error: Expression
  decide
    (trun 1 (borrowed, [], env0, borrowedAcct, dropStoreTerm)
      = (borrowed, [], env0, borrowedAcct, storeTerm))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (trun 1 (borrowed, [], env0, borrowedAcct, dropStoreTerm)
  = (borrowed, [], env0, borrowedAcct, storeTerm))

/-! ## The discipline's own clause, refused

The clause a write has to satisfy is stated at the term, so a write whose subject's name
occurs twice among the term's free occurrences, and one whose subject is not a variable, are
refused as theorems. Each stands beside the affirmative control at the same shape: the write
whose subject occurs once. -/

/-- The write the checks read satisfies the write clause: its subject occurs once among its
free occurrences. -/
theorem owned_writes_owned : WritesOwned storeTerm := by
  change WritesOwned (.store (.var 0) 0 (.var 2))
  rw [writesOwned_store_var]
  exact ⟨by decide, trivial⟩

/-- A write whose value names the subject is refused: the subject's name occurs twice among
the term's free occurrences. -/
theorem duplicated_subject_not_writesOwned : ¬ WritesOwned twiceSubject := by
  change ¬ WritesOwned (.store (.var 0) 0 (.var 0))
  rw [writesOwned_store_var]
  simp [WritesOwned, uses]

/-- A write whose subject is not a variable is refused: the write clause asks for the
subject to be a variable. -/
theorem not_var_subject_not_writesOwned : ¬ WritesOwned notVarSubject := by
  simp [WritesOwned, notVarSubject]

/-- The affirmative control beside the two refusals, read through the traverse: the write
whose subject is a variable occurring once. -/
theorem single_subject_writes_owned : WritesOwned storeTerm := owned_writes_owned

/-- The traverse reads a term with no write as disciplined: a term that mentions no write
at all satisfies the clause. -/
theorem no_write_writes_owned : WritesOwned (.drop 0 (.con0 5)) := trivial

/-! ## The coupling invariant at the two configurations -/

/-- A heap is counted when every cell it lists carries the count its occurrences and its
hands give it, every slot names a cell it lists, and every reference the term holds names
one. These are the three conditions a reader can check at a small heap. -/
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

/-- The disciplined configuration's heap is counted at the term's own references. -/
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

/-- The disciplined configuration's heap is well formed. -/
theorem owned_wf : CHeap.WF owned := by rw [CHeap.WF]; decide

/-- The term's own references name, each pair, the reference the environment binds its
variable to. -/
theorem acct_bound : Bound env0 acct := by
  intro p hp
  have hp' : p = (0, 0) ∨ p = (2, 2) := by simpa [acct] using hp
  rcases hp' with rfl | rfl <;> decide

/-- The disciplined configuration satisfies the coupling invariant. -/
theorem owned_couple : Couple owned [] env0 acct :=
  ⟨owned_wf, owned_counted, acct_bound⟩

/-- The borrowed configuration's heap is counted at the reading in which the subject is held
twice. -/
theorem borrowed_counted : Counted borrowed ([] ++ expand borrowedAcct) := by
  refine counted_of borrowed ([] ++ expand borrowedAcct) ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by simpa [borrowed] using hx
    rcases hx' with rfl | rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 1 ∨ x = 2 := by simpa [borrowed] using hx
    rcases hx' with rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 0 ∨ x = 2 := by simpa [borrowedAcct] using hx
    rcases hx' with rfl | rfl <;> decide

/-- The borrowed configuration's heap is well formed. -/
theorem borrowed_wf : CHeap.WF borrowed := by rw [CHeap.WF]; decide

/-- The borrowed reading's pairs name the reference the environment binds their variable
to. -/
theorem borrowedAcct_bound : Bound env0 borrowedAcct := by
  intro p hp
  have hp' : p = (0, 0) ∨ p = (2, 2) := by
    rw [borrowedAcct] at hp
    simpa using hp
  rcases hp' with rfl | rfl <;> decide

/-- The borrowed configuration satisfies the coupling invariant: it is a configuration the
write's rules are stated about, and the discipline is what it fails. -/
theorem borrowed_couple : Couple borrowed [] env0 borrowedAcct :=
  ⟨borrowed_wf, borrowed_counted, borrowedAcct_bound⟩

/-- The root's shape at the disciplined configuration: no slot and no handle names the
subject's cell. -/
theorem owned_rooted : Rooted owned [] 0 := by
  constructor <;> decide

/-- The root's shape read as the two facts the composition needs: the heap's slots and the
run's handles count the subject's cell zero. -/
theorem owned_rooted_counts :
    (CHeap.slots owned).count 0 = 0 ∧ ([] : List Ref).count 0 = 0 :=
  ⟨Rooted.slot_count owned_rooted, Rooted.handle_count owned_rooted⟩

/-! ## The discipline at the two configurations

The pair is the countermodel: one term, two configurations, and the subject's cell carrying
one occurrence at the first and two at the second. -/

/-- The term's free occurrences at the write, read at the references and at the pairs. -/
theorem refs_store : refsOf env0 (uses storeTerm) = [0, 2] := by decide

/-- The pairs the write's free occurrences name. -/
theorem occs_store : occsOf env0 storeTerm = [(0, 0), (2, 2)] := by decide

/-- The write's own account is the account of its free occurrences. -/
theorem acct_account : AccountOf env0 storeTerm acct := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    rw [show expand acct = [0, 2] from by decide, refs_store]
  · intro p
    rw [← occsOf_pairsOf, occs_store]
    exact Nat.le_refl _
  · intro x hx
    rw [show uses storeTerm = [0, 2] from by decide] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨0, by decide⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨2, by decide⟩
    simp at hx

/-- The environment's reading of the write's free occurrences is injective: the two names
it reads are read at distinct references. -/
theorem storeTerm_injective : InjectiveOn env0 storeTerm := by
  intro x hx z hz h
  rw [show uses storeTerm = [0, 2] from by decide] at hx hz
  rcases List.mem_cons.mp hx with rfl | hx
  · rcases List.mem_cons.mp hz with rfl | hz
    · rfl
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact absurd h (by decide)
      · simp at hz
  · rcases List.mem_cons.mp hx with rfl | hx
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact absurd h.symm (by decide)
      · rcases List.mem_cons.mp hz with rfl | hz
        · rfl
        · simp at hz
    · simp at hx

/-- The disciplined configuration is `WellFormed`: the account is the term's own
occurrences, the environment's reading of them is injective, and the write's subject occurs
once. -/
theorem acct_wellFormed : WellFormed env0 acct storeTerm :=
  ⟨acct_account, storeTerm_injective, owned_writes_owned⟩

/-- The borrowed configuration is not `WellFormed`: the account counts the subject's cell
twice while the term has the subject's occurrence once, so the account is not the term's own
references. This is the countermodel's point — the discipline is what refuses it. -/
theorem borrowed_not_wellFormed : ¬ WellFormed env0 borrowedAcct storeTerm := by
  intro h
  have hrefs : (expand borrowedAcct).count 0 = (refsOf env0 (uses storeTerm)).count 0 :=
    h.account.refs 0
  rw [show expand borrowedAcct = [0, 0, 2] from by decide, refs_store] at hrefs
  simp at hrefs

/-- The account of the store term is its own references: the affirmative counterpart of the
refusal beside it, read as the account relation rather than as the discipline. -/
theorem borrowed_not_account : ¬ AccountOf env0 storeTerm borrowedAcct :=
  fun h => borrowed_not_wellFormed ⟨h, storeTerm_injective, owned_writes_owned⟩

/-! ## The three theorems applied

The discipline's implication for the store's hypotheses, the release's move, and the
composition at the root. -/

/-- The discipline at the write gives the pair's ownership and the subject's reference
counted once: the two hypotheses `Ownership.store_owned_is_destructive` consumes. -/
theorem store_ownership : Owns env0 acct storeTerm
    ∧ ∃ r, env0.lookup 0 = some r ∧ (expand acct).count r = 1 :=
  wellFormed_store acct_wellFormed

/-- The write's ownership, read as the pair the account holds. -/
theorem store_owns_holds : Owns env0 acct storeTerm := (store_ownership).1

/-- The discipline at the release of the subject's occurrence: the release's own occurrence
is counted as well, so the configuration is the borrowed one. -/
theorem release_wellFormed : WellFormed env0 borrowedAcct dropStoreTerm := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro r
      rw [show expand borrowedAcct = [0, 0, 2] from by decide,
        show refsOf env0 (uses dropStoreTerm) = [0, 0, 2] from by decide]
    · intro p
      rw [← occsOf_pairsOf, show occsOf env0 dropStoreTerm = [(0, 0), (0, 0), (2, 2)] from by decide]
      exact Nat.le_refl _
    · intro x hx
      rw [show uses dropStoreTerm = [0, 0, 2] from by decide] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨0, by decide⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨0, by decide⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨2, by decide⟩
      simp at hx
  · intro x hx z hz h
    rw [show uses dropStoreTerm = [0, 0, 2] from by decide] at hx hz
    rcases List.mem_cons.mp hx with rfl | hx
    · rcases List.mem_cons.mp hz with rfl | hz
      · rfl
      · rcases List.mem_cons.mp hz with rfl | hz
        · rfl
        · rcases List.mem_cons.mp hz with rfl | hz
          · exact absurd h (by decide)
          · simp at hz
    · rcases List.mem_cons.mp hx with rfl | hx
      · rcases List.mem_cons.mp hz with rfl | hz
        · rfl
        · rcases List.mem_cons.mp hz with rfl | hz
          · rfl
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact absurd h (by decide)
            · simp at hz
      · rcases List.mem_cons.mp hx with rfl | hx
        · rcases List.mem_cons.mp hz with rfl | hz
          · exact absurd h.symm (by decide)
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact absurd h.symm (by decide)
            · rcases List.mem_cons.mp hz with rfl | hz
              · rfl
              · simp at hz
        · simp at hx
  · exact owned_writes_owned

/-- The release's move with the discipline standing at both ends: the release of the
subject's occurrence leaves the disciplined configuration, and the move is the one
`Target.TStep.dropShared` makes at the borrowed heap. -/
theorem release_moves : WellFormed env0 (Multi.dropOcc borrowedAcct 0 0) storeTerm :=
  wellFormed_drop release_wellFormed (by decide) (by decide)

/-- The release's move read at the step relation, with the discipline's own move as its
conclusion: the configuration `Target.TStep.dropShared` leaves is the one the discipline is
preserved to, up to the two readings of the moved occurrence. -/
theorem release_step : TStep borrowed [] env0 borrowedAcct dropStoreTerm
    (decRef borrowed [] 0).1 [] env0 (Multi.dropOcc borrowedAcct 0 0) storeTerm :=
  TStep.dropShared (by decide) (by decide) (by decide)

/-- The configuration the release's step leaves is `WellFormed`, read at the step's own
heap: `Target.TStep.dropShared` is the rule that leaves the configuration the run above
reaches, so the discipline stands at both ends of that step. -/
theorem release_step_of_rule :
    WellFormed env0 (Multi.dropOcc borrowedAcct 0 0) storeTerm :=
  wellFormed_dropShared (c := borrowed) (by decide) (by decide) (by decide) release_wellFormed

/-- The composition at the root: the disciplined write at the root of the coupled
configuration keeps the cell's location. -/
theorem composed_keeps :
    (update owned ([] ++ expand acct) 0 [2, 2]).1.lookup 0 = some [2, 2] :=
  rooted_store_destructive owned_couple (by decide) acct_wellFormed owned_rooted (by decide)

/-- The same conclusion through the store theorem the composition reads, with the pieces the
discipline gives it read out one by one. -/
theorem composed_keeps_ownership :
    (update owned ([] ++ expand acct) 0 [2, 2]).1.lookup 0 = some [2, 2] := by
  obtain ⟨hown, r, hr, hcount⟩ := store_ownership
  have h0 : env0.lookup 0 = some 0 := by decide
  have hrr : r = 0 := (Option.some.inj (by rw [h0] at hr; exact hr)).symm
  exact store_owned_is_destructive owned_couple (by decide) hown (by rw [← hrr]; exact hcount)
    (by decide) (by decide) (by decide)

/-- The borrowed configuration's write copies: its cell is at a count other than one, so
the written slots land at the heap's fresh location, the old cell keeps its slots, and it
loses a reference. The discipline refuses this configuration, and the write copies. -/
theorem borrowed_copies :
    (update borrowed ([] ++ expand borrowedAcct) 0 [2, 2]).1.lookup
        (fresh borrowed [2, 2]) = some [2, 2]
      ∧ (update borrowed ([] ++ expand borrowedAcct) 0 [2, 2]).1.lookup 0
          = CHeap.lookup borrowed 0
      ∧ (update borrowed ([] ++ expand borrowedAcct) 0 [2, 2]).1.count 0
          = CHeap.count borrowed 0 - 1 :=
  store_shared_copies borrowed_couple (by decide)
    (Owns.store (y := 0) (r := 0) (i := 0) (v := .var 2) (by decide) (by decide))
    (by decide) (by decide)

/-! ## The moves the account does not make, at concrete terms -/

/-- The account the `dup` rule leaves is one occurrence above the body's own: the rule
supplies an occurrence the body does not have, which is why no step of that shape preserves
the discipline. -/
theorem dup_move_above :
    AccountOf env0 storeTerm (Multi.dropOcc (Multi.insert acct 0 0) 0 0)
      ∧ ¬ AccountOf env0 storeTerm (Multi.insert acct 0 0) :=
  accountOf_dupStep acct_account (by decide)

/-- The account the `dup` rule leaves, read at the body: it is the body's own account, so
the move the rule makes is the account's own, which is what the discipline does not
preserve. -/
theorem dup_move_body : AccountOf env0 storeTerm (Multi.dropOcc (Multi.insert acct 0 0) 0 0) :=
  dup_move_above.1

/-- The store's account is not the result's own: the account holds the value's occurrence
and the result's own account holds none of it. -/
theorem store_move_wider : ¬ AccountOf env0 (.var 0) acct :=
  accountOf_storeStep acct_account storeTerm_injective (z := 2) (s := 2)
    (by decide) (by decide) (by decide)

/-- The result's own account is the subject's pair, which is the ownership the store
theorem reads: the affirmative counterpart of the refusal beside it. -/
theorem result_account : AccountOf env0 (.var 0) [(0, 0)] :=
  accountOf_var (by decide)

/-- The two account terms the store's move relates: the account the rule leaves is the
store's own account, and the result's own is the subject's pair. -/
theorem store_move_pair :
    AccountOf env0 (.var 0) [(0, 0)] ∧ ¬ AccountOf env0 (.var 0) acct :=
  ⟨result_account, store_move_wider⟩

/-! ## Axioms of representative theorems -/

/--
info: 'Scidonia.RC.wellFormed_store' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wellFormed_store

/--
info: 'Scidonia.RC.accountOf_dropStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms accountOf_dropStep

/--
info: 'Scidonia.RC.accountOf_bindVar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms accountOf_bindVar

/--
info: 'Scidonia.RC.accountOf_dupStep' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms accountOf_dupStep

/--
info: 'Scidonia.RC.accountOf_storeStep' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms accountOf_storeStep

/--
info: 'Scidonia.RC.wellFormed_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wellFormed_drop

/--
info: 'ScidoniaTest.Discipline.owned_writes_owned' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms owned_writes_owned

/--
info: 'ScidoniaTest.Discipline.borrowed_not_wellFormed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms borrowed_not_wellFormed

/--
info: 'ScidoniaTest.Discipline.composed_keeps' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms composed_keeps

/--
info: 'ScidoniaTest.Discipline.borrowed_copies' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms borrowed_copies

end ScidoniaTest.Discipline
