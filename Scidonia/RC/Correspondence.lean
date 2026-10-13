/-
The correspondence between the typing's environments and the target's account: the
link that turns a typed store into the two hypotheses the target's write theorem
consumes.

`Scidonia.RC.Typing` says which source terms are written to reach a reference-counted
target, and what its write's clause counts is a *name*: a store is typed at an
environment that holds its subject's name exactly once. `Scidonia.RC.Ownership`'s
`store_owned_is_destructive` says what the target's write does at a subject the term's
own account holds once and counts once, and its two premises --- the term's own
occurrence of the subject (`Owns`) and the account's count of the reference the
target's environment names for it --- are premises nothing in this development derives
from a typing: the typing's environment is a list of names, the target's is a list of a
name and a reference, and the term's own account is a list of such pairs. This module
is that link, as a *correspondence* between the two readings under which a typed
store's two premises follow from the typing's own write clause.

**Why a correspondence, and not the judgement.** `Scidonia.RC.Discipline`'s `Runs` was
built to be the link --- a term run at an account, one clause per construct, each the
premise of the target rule that construct takes together with the account movement that
rule makes --- and it is a sufficient condition *at a store* rather than the
source-to-target link, which is a checked fact rather than an argument:
`ScidoniaTest/Target`'s `source_typed` and `lowered_not_runs` stand beside each other,
the source typed at `[]`, `[0, 1, 2]` and its canonical lowering *not* judged, because
`Runs.bindVal` demands the resumed write at every reference the binder could take and
the instance at `r = 2` counts that reference three times. The judgement's binding
clause is universally quantified over the binder's reference while the rule resumes at
the one reference its realisation returns, so at a lowering the clause asks for a state
the run never reaches. The correspondence below is read against the typing and at the
configuration the run *does* reach.

**The correspondence.** `Corr ρ m Γ` says three things of the target's environment `ρ`,
the term's own account `m` and the typing's environment `Γ`:

* every pair of the account names the reference the environment binds its name to
  (`Bound`, which `Ownership.Couple` already carries);
* the account's multiplicity at each *name* is the typing's count of that name, which
  makes `Γ` the typing's reading of the account rather than a second object;
* the account's tags are injective on references (`RefInj`): two pairs naming one
  reference carry one name.

A store typed at `Γ` whose environment counts its subject once --- the typing's own
write clause --- then meets `store_owned_is_destructive`'s two premises, which is the
bridge below, and the write theorem's branch follows, which is
`store_destructive_of_typed`.

**What the correspondence carries, and what it does not.** `bound` and `name` are what
the typing and the target's environment supply: `Bound` is the coupling invariant's own
clause, and the name count is the typing's environment read against the account.
Reference-injectivity is supplied by *neither* `Typed` nor `Couple`, and the witness is
the two-names-one-reference configuration below (`aliasEnv`, `aliasM`): the names `0`
and `1` both name the reference `0`, the store at the subject `0` is typed at `[]`,
`[0, 1]` --- its subject owned exactly once there and not borrowed --- the account is
`Bound` and the whole coupling invariant stands at one cell of count two, and the
account counts the reference twice, so the count of one the write needs does not
follow. `couple_does_not_give_count_one` is that statement, and
`count_one_fails_without_inj` is the same refutation as the negation of the bridge's
second conclusion. What would supply the injectivity is a distinctness or a freshness
condition on the environment the program starts from --- no two of its names naming one
reference --- or the same condition read at the take-out of a nested write, where the
cell's count of one and the absence of a second name for it are facts the take-out
provides; neither is in this slice.

**The affirmative side, and where it is checked.** The accounts the lowering's prologue
and the source's own environment leave *are* injective, the bridge applies at the
configuration a lowered run reaches, and the typing refuses the sibling term whose
account would hold a name twice --- together with the evaluated readings of
`countName`, `RefInj` and the reference counts, those are `ScidoniaTest/Correspondence`'s
checks, and the module's negative controls above are read beside them.

**`Runs` is unchanged, and it is not this route.** Nothing here edits the judgement, its
clauses or its theorems. It remains the target-side sufficient condition at a store
that `runs_store_owned` reads the write's two hypotheses off, and it holds at the
configuration a lowered run actually reaches (`ScidoniaTest/Correspondence`'s
`runs_at_actual`); what fails at a lowering is the universally quantified obligation of
its binding clause, at a reference the run never binds. The two are routes of different
kinds --- a judgement of the target's relation, and a correspondence between the
typing's environments and the account --- and the source's link is the correspondence.

**What is modelled, and what is trusted.** The correspondence is a relation between the
typing's environments and the target's account and not a computation on either: nothing
here derives an account from a term, and the account's name counts are read as multiset
counts in list form, exactly as the typing's environments are. Reference-injectivity is
a property of the account and not of the heap, and it is what the typing's name counts
and the coupling invariant leave open. The composition's remaining hypotheses are
`store_owned_is_destructive`'s own, named there as what the discipline's take-out
provides and what the write rule's check demands. Nothing here is about compiled code.
-/
import Scidonia.RC.Discipline
import Scidonia.RC.Typing

namespace Scidonia.RC

open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap

/-! ## The account's multiplicity at a name, and reference-injectivity

The typing counts *names* (`Γ.count y`) and the write theorem counts *references*
(`(expand m).count r`), so the correspondence is stated with both readings of the
account: how many of its pairs carry a name, and whether two of its pairs that name one
reference carry one name. -/

/-- The account's multiplicity at a name: how many of the account's pairs carry that
name. It is the reading the typing's `Γ.count` is compared against --- `Γ.count` is a
count of the environment's names, and this is that count read off the term's own
pairs. -/
def countName (m : Multi) (x : Var) : Nat := (m.filter (fun p => p.1 = x)).length

/-- The account's tags are injective on references: two pairs of the account that name
one reference carry one name. This is the runtime's freshness discipline read as a
property of the account, and it is the clause `Bound` together with the name counts do
not supply --- two distinct names may name one reference, which is the configuration
the negative controls below exhibit. -/
def RefInj (m : Multi) : Prop := ∀ p ∈ m, ∀ q ∈ m, p.2 = q.2 → p.1 = q.1

/-- The correspondence between the typing's environment `Γ` and the target's account
`(ρ, m)`: every pair of the account names the reference the environment binds its name
to, the account's multiplicity at each name is the typing's count of that name, and the
account's tags are injective on references. Under it, a store's own write clause gives
the target write theorem's two hypotheses (`bridge`). -/
structure Corr (ρ : TEnv) (m : Multi) (Γ : Occs) : Prop where
  /-- Every pair of the account names the reference the environment binds its name
  to. -/
  bound : Bound ρ m
  /-- The account's multiplicity at each name is the typing's count of that name. -/
  name : ∀ x, countName m x = Γ.count x
  /-- The account's tags are injective on references. -/
  inj : RefInj m

/-! ## The counts, and the accounts a list of names reads as -/

/-- The account's count of a reference, read as a filter: the length of the account's
pairs that name that reference. It is the reference-side reading `countName` is at the
names' side of. -/
theorem count_expand (m : Multi) (r : Ref) :
    (expand m).count r = (m.filter (fun p => decide (p.2 = r))).length := by
  induction m with
  | nil => rfl
  | cons p t ih =>
      obtain ⟨a, s⟩ := p
      by_cases hs : s = r
      · subst hs
        rw [expand_cons, List.count_cons_self, ih, List.filter_cons_of_pos (by simp)]
        simp [List.length_cons]
      · rw [expand_cons, List.count_cons_of_ne (a := r) (b := s) hs, ih,
          List.filter_cons_of_neg (by simp [hs])]

/-- A pair prepended to the account adds one to its name's multiplicity exactly when
the pair carries that name. -/
theorem countName_cons (p : Var × Ref) (m : Multi) (x : Var) :
    countName (p :: m) x = (if p.1 = x then 1 else 0) + countName m x := by
  obtain ⟨a, b⟩ := p
  unfold countName
  by_cases h : a = x
  · rw [List.filter_cons_of_pos (by simp [h]), List.length_cons]
    have : (if a = x then 1 else 0) = 1 := by simp [h]
    rw [this]
    omega
  · rw [List.filter_cons_of_neg (by simp [h])]
    have : (if a = x then 1 else 0) = 0 := by simp [h]
    rw [this]
    omega

/-- An occurrence the account holds makes its name's multiplicity positive. -/
theorem countName_pos {m : Multi} {y : Var} {r : Ref} (h : (y, r) ∈ m) :
    0 < countName m y := by
  unfold countName
  rw [List.length_pos_iff_exists_mem]
  exact ⟨(y, r), by rw [List.mem_filter]; exact ⟨h, by simp⟩⟩

/-- A name's multiplicity of one is an occurrence of that name: a count of one names
the pair the account holds. -/
theorem countName_one_pair {m : Multi} {y : Var} (h : countName m y = 1) :
    ∃ r, (y, r) ∈ m := by
  unfold countName at h
  obtain ⟨⟨a, b⟩, hq⟩ := List.length_eq_one_iff.mp h
  have hmem : (a, b) ∈ m.filter (fun p => p.1 = y) := by rw [hq]; simp
  rw [List.mem_filter] at hmem
  have h1 : a = y := of_decide_eq_true hmem.2
  exact ⟨b, by simpa [h1] using hmem.1⟩

/-- The account's multiplicity at a name is the count of the account's tags: the two
readings of the account's names agree. -/
theorem countName_eq_count_fst (m : Multi) (x : Var) :
    countName m x = (m.map Prod.fst).count x := by
  unfold countName
  induction m with
  | nil => rfl
  | cons p t ih =>
      obtain ⟨a, b⟩ := p
      by_cases h : a = x
      · subst h
        rw [List.filter_cons_of_pos (by simp), List.length_cons, List.map_cons]
        simp only [List.count_cons_self]
        rw [ih]
      · rw [List.filter_cons_of_neg (by simp [h])]
        simp only [List.map_cons, List.count_cons_of_ne h, ih]

/-- **The count of one at a reference.** Under injectivity, the account's counting the
subject's name once makes it count the subject's reference once: injectivity puts every
pair naming that reference at the subject's name, and the name's count says there is
exactly one such pair. -/
theorem count_expand_one {m : Multi} {y : Var} {r : Ref}
    (hinj : RefInj m) (hmem : (y, r) ∈ m) (hcount : countName m y = 1) :
    (expand m).count r = 1 := by
  induction m with
  | nil => simp at hmem
  | cons p t ih =>
      obtain ⟨a, s⟩ := p
      rw [expand_cons]
      have hcn : countName ((a, s) :: t) y = (if a = y then 1 else 0) + countName t y :=
        countName_cons (a, s) t y
      by_cases hs : s = r
      · subst hs
        rw [List.count_cons_self]
        have hz : List.count s (expand t) = 0 := by
          rw [List.count_eq_zero]
          intro hmem_exp
          obtain ⟨q, hq, hq2⟩ := List.mem_map.mp hmem_exp
          have hay : a = y := hinj (a, s) (List.mem_cons_self ..) (y, s) hmem (by simp)
          have hqy : q.1 = y :=
            hinj q (List.mem_cons_of_mem _ hq) (y, s) hmem (by rw [hq2])
          have hzero : countName t y = 0 := by
            have h1 : countName ((a, s) :: t) y = 1 + countName t y := by
              rw [hcn]; simp [hay]
            omega
          have hpos : 0 < countName t y := by
            refine countName_pos (m := t) (y := y) (r := q.2) ?_
            rw [← hqy]; exact hq
          omega
        omega
      · rw [List.count_cons_of_ne (a := r) (b := s) hs]
        have hmem' : (y, r) ∈ t := by
          rcases List.mem_cons.mp hmem with heq | hmem'
          · exact absurd (congrArg Prod.snd heq) (fun hh => hs hh.symm)
          · exact hmem'
        have hcount' : countName t y = 1 := by
          by_cases hay : a = y
          · have h1 : countName ((a, s) :: t) y = 1 + countName t y := by
              rw [hcn]; simp [hay]
            have hpos : 0 < countName t y := countName_pos hmem'
            omega
          · have h0 : countName ((a, s) :: t) y = 0 + countName t y := by
              rw [hcn]; simp [hay]
            omega
        exact ih (fun p hp q hq heq =>
          hinj p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq) heq) hmem' hcount'

/-- The pairs a list of names names satisfy `Bound`: every pair it lists is read at the
reference the environment binds its name to, because the pair *is* the name and that
reference. The reading `m = pairsOf ρ Γ` therefore always satisfies the correspondence's
first clause and never its third one, which is what the checks read at the account a
binding would leave. -/
theorem pairsOf_bound (ρ : TEnv) (us : List Var) : Bound ρ (pairsOf ρ us) := by
  intro p hp
  simp only [pairsOf, List.mem_filterMap] at hp
  obtain ⟨x, _hx, hmap⟩ := hp
  cases hlook : ρ.lookup x with
  | none => simp [hlook] at hmap
  | some r =>
      have hp' : p = (x, r) := (Option.some.inj (by simpa [hlook] using hmap)).symm
      rw [hp']
      exact hlook

/-! ## The bridge

The typing's write clause is a count of a name, and the target's write theorem needs a
count of a reference beside the term's own occurrence. The correspondence turns the
first into both. -/

/-- A typed store owns its subject's name exactly once at the store's environment: the
typing's own write clause, read off the derivation. -/
theorem Typed.store_count {Δ Γ : Occs} {y : Var} {i : Nat} {v : Expr}
    (h : Typed Δ Γ (.store (.var y) i v)) : Γ.count y = 1 := by
  cases h with
  | store hown _ _ => exact hown

/-- The account's occurrence of the subject, from the weaker correspondence: `Bound`
and the name count alone already give `Owns`, because the account holds exactly one
occurrence of the subject's name and `Bound` reads that occurrence's reference off the
environment. This is the half of the bridge that needs no injectivity, and it is why
the two controls below separate on the count of the reference and not on the
occurrence. -/
theorem owns_of_correspondence {ρ : TEnv} {m : Multi} {Γ : Occs} {y : Var} {r : Ref}
    {i : Nat} {v : Expr} (hbound : Bound ρ m) (hname : countName m y = Γ.count y)
    (hone : Γ.count y = 1) (hlook : ρ.lookup y = some r) :
    Owns ρ m (.store (.var y) i v) := by
  have hcy : countName m y = 1 := by rw [hname, hone]
  obtain ⟨r', hmem⟩ := countName_one_pair hcy
  have hr' : r' = r := Option.some.inj ((hbound (y, r') hmem).symm.trans hlook)
  exact Owns.store hlook (by rw [← hr']; exact hmem)

/-- The bridge: a store typed at `Γ`, whose environment `Γ` counts its subject once,
at a configuration corresponding to `(ρ, m)` in the sense of `Corr`, meets the target
write theorem's two premises --- the account holds the subject's occurrence (`Owns`),
and the account counts the reference the environment names for it exactly once. -/
theorem bridge {ρ : TEnv} {m : Multi} {Γ : Occs} {y : Var} {r : Ref} {i : Nat} {v : Expr}
    (h : Corr ρ m Γ) (hlook : ρ.lookup y = some r) (hone : Γ.count y = 1) :
    Owns ρ m (.store (.var y) i v) ∧ (expand m).count r = 1 := by
  have hcy : countName m y = 1 := by rw [h.name y, hone]
  obtain ⟨r', hmem⟩ := countName_one_pair hcy
  have hmem' : (y, r) ∈ m := by
    have hb := h.bound (y, r') hmem
    have hrr : r' = r := Option.some.inj (hb.symm.trans hlook)
    rw [← hrr]; exact hmem
  exact ⟨Owns.store hlook hmem', count_expand_one h.inj hmem' hcy⟩

/-! ## Two names at one reference

The clause the correspondence needs and the typing does not supply, at the smallest
configuration that separates them: two names of the environment name one reference. The
store is typed (its subject is owned once), the account's tags name the environment's
references, the couplings hold, and the account counts the reference twice --- so the
count of one the write theorem needs is not a consequence of `Typed` and `Couple`
without the injectivity. -/

/-- The environment of the refutation: the names `0` and `1` both name the reference
`0`. -/
def aliasEnv : TEnv := [(0, 0), (1, 0)]

/-- The account of the refutation: one occurrence of each of the two names, both at the
reference `0`. -/
def aliasM : Multi := [(0, 0), (1, 0)]

/-- The refutation's store is typed at `[]`, `[0, 1]`: its subject is owned exactly once
there and not borrowed, and its value is a node. -/
theorem alias_typed : Typed ([] : Occs) ([0,1] : Occs) (.store (.var 0) 0 (.con0 9)) := by
  refine Typed.store (hown := by decide) (hborrow := by decide) ?_
  exact Typed.con0

/-- The account names, each pair, the reference the environment binds its name
to. -/
theorem alias_bound : Bound aliasEnv aliasM := by
  intro p hp
  simp [aliasM] at hp
  rcases hp with rfl | rfl <;> decide

/-- The refutation's configuration satisfies the *whole* coupling invariant: one cell
at a count of two, the heap well formed, its counts the account's own references, and
the tags naming the environment's references. -/
theorem alias_couple : Couple ([(0, { slots := [], count := 2 })] : CHeap) [] aliasEnv aliasM := by
  refine ⟨?_, ?_, alias_bound⟩
  · rw [CHeap.WF]; decide
  · rw [counted_iff_slots]
    intro x
    by_cases hx : x = 0
    · subst hx; decide
    · have hcount : CHeap.count ([(0, { slots := [], count := 2 })] : CHeap) x = 0 :=
        CHeap.count_eq_zero_of_not_mem (by simpa using hx)
      have hhandles : List.count x (expand aliasM) = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        exact hx (by simpa [aliasM, expand] using hmem)
      simp [hcount, hhandles]

/-- The account's name counts match the typing's `Γ = [0, 1]` at the subject's
name. -/
theorem alias_name_count : countName aliasM 0 = ([0,1] : Occs).count 0 := by decide

/-- The account gives the reference `0` a count of two: injectivity is exactly what is
falsified here, and nothing else in the typing or the coupling refuses the
configuration. -/
theorem alias_ref_count_two : (expand aliasM).count (0 : Ref) = 2 := by decide

/-- The account is not injective: its two names name one reference. -/
theorem alias_not_inj : ¬ RefInj aliasM := by
  intro h
  have h01 : (0 : Var) = 1 := h (0, 0) (by decide) (1, 0) (by decide) rfl
  exact absurd h01 (by decide)

/-- The refutation in one statement: a typed store, an account that satisfies the
correspondence's `Bound` and name-count clauses, and a reference the account counts
twice. So the count of one the write theorem needs is *not* a consequence of `Typed`
plus the correspondence minus injectivity. -/
theorem alias_kills_bridge :
    Typed ([] : Occs) ([0,1] : Occs) (.store (.var 0) 0 (.con0 9))
      ∧ Bound aliasEnv aliasM
      ∧ countName aliasM 0 = ([0,1] : Occs).count 0
      ∧ (expand aliasM).count (0 : Ref) = 2 :=
  ⟨alias_typed, alias_bound, alias_name_count, alias_ref_count_two⟩

/-- The same refutation as the exact negation of the bridge's second conclusion: there
are a typed store and a configuration satisfying every correspondence hypothesis but
injectivity at which the account does not count the environment's reference
once. -/
theorem count_one_fails_without_inj :
    ∃ (ρ : TEnv) (m : Multi) (Γ : Occs) (y : Var) (r : Ref) (i : Nat) (v : Expr),
      Typed ([] : Occs) Γ (.store (.var y) i v) ∧ Bound ρ m
        ∧ countName m y = Γ.count y ∧ ρ.lookup y = some r ∧ (expand m).count r ≠ 1 :=
  ⟨aliasEnv, aliasM, [0,1], 0, 0, 0, .con0 9, alias_typed, alias_bound, alias_name_count,
    by decide, by decide⟩

/-- The same refutation with the *whole* coupling invariant standing: `Couple` (hence
`Bound` and the heap's counts), `Typed` and the name counts all hold, and the reference
is still counted twice. So neither `Typed`, nor `Couple`, nor their conjunction supplies
the injectivity; only `RefInj` does. -/
theorem couple_does_not_give_count_one :
    Couple ([(0, { slots := [], count := 2 })] : CHeap) [] aliasEnv aliasM
      ∧ Typed ([] : Occs) ([0,1] : Occs) (.store (.var 0) 0 (.con0 9))
      ∧ countName aliasM 0 = ([0,1] : Occs).count 0
      ∧ (expand aliasM).count (0 : Ref) ≠ 1 :=
  ⟨alias_couple, alias_typed, alias_name_count, by decide⟩

/-- A binding of a variable breaks injectivity at an account that already holds a name
twice: the binder's pair joins the surviving occurrence at the same reference. It is
the other direction the clause `Corr` reads --- injectivity is not preserved by every
move of the relation --- and the prologue's releases are what leave a lowered run's
accounts injective, which the checks read at the account the prologue leaves. -/
theorem bindVar_breaks_inj :
    RefInj ([(1,0),(1,0)] : Multi)
      ∧ ¬ RefInj (Multi.insert (Multi.dropOcc ([(1,0),(1,0)] : Multi) 1 0) 2 0) := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq heq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rfl
  · intro h
    have h21 : (2 : Var) = 1 := h (2, 0) (by decide) (1, 0) (by decide) rfl
    exact absurd h21 (by decide)

/-! ## The composition with the target's write theorem -/

/-- A typed store is destructive at a corresponding configuration: the typing's write
clause and the correspondence give `store_owned_is_destructive`'s two premises, and the
theorem gives the branch --- the cell the subject names keeps its location and holds the
written slots. The hypotheses `hslot`, `hrun` and `hks` are that theorem's own, named
there as what the discipline's take-out provides and what the write rule's check
demands; the conclusion is that theorem's. -/
theorem store_destructive_of_typed {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi}
    {Δ Γ : Occs} {y : Var} {r : Ref} {i : Nat} {v : Expr} {ks : List Ref}
    (hc : Couple c hs ρ m) (hcorr : Corr ρ m Γ) (hlook : ρ.lookup y = some r)
    (h : Typed Δ Γ (.store (.var y) i v))
    (hslot : (CHeap.slots c).count r = 0) (hrun : hs.count r = 0) (hks : r ∉ ks) :
    (update c (hs ++ expand m) r ks).1.lookup r = some ks := by
  obtain ⟨hown, hcount⟩ := bridge (i := i) (v := v) hcorr hlook (Typed.store_count h)
  exact store_owned_is_destructive hc hlook hown hcount hslot hrun hks

end Scidonia.RC
