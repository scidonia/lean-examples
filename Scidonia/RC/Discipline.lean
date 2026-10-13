/-
The discipline the target's write needs: what a term's own references *are*, the clause a
write's subject has to satisfy, and the condition on the environment under which "once in
the term" means "once in the account".

`Scidonia.RC.Ownership` states what the target's write does at a subject the term owns
once and what it does otherwise, but its two premises --- the term's own occurrence of the
subject (`Owns`) and the account counting that occurrence once --- are premises nothing in
the development supplies. This module supplies them. It fixes what a term's account *is*:
the term's free occurrences, read through the environment (`AccountOf`); the clause a
write's subject has to satisfy (`WritesOwned`: the subject is a variable, and it occurs
exactly once among the term's free variables); and the condition on the environment under
which "once in the term" means "once in the account" (`InjectiveOn`: distinct free
variables of the term name distinct references). `WellFormed` is the three together.

**The account is the term's own references.** `Scidonia.RC.uses` gives the term's free
occurrences as a multiset in list form; `refsOf` reads a list of names at the references
the environment binds them to, and `pairsOf` reads the same list at the pairs --- the name
and its reference --- which is what makes a *pair*, and not merely a count, readable out
of the account. `AccountOf` says the account's references are the term's free occurrences
read through the environment (the clause `Ownership`'s store theorems are stated about),
that the account's pairs are pairs the term's own occurrences name (so the account's tags
are the term's names, and `Ownership`'s `Bound` follows), and that the environment reads
every free variable of the term. A count alone is not enough for a store: it says how many
occurrences name a reference, not which variable holds it, and `Owns` needs the pair.

**The account of a construct, and the moves of the rules.** The account of a term is read
off its subterms, one lemma per constructor (`accountOf_var`, `accountOf_con0`,
`accountOf_of_closed` for the leaves; `accountOf_app`, `accountOf_con1`, `accountOf_con2`,
`accountOf_store`, `accountOf_dup`, `accountOf_drop`). The runtime's own rules move the
account where they move one occurrence with the term: the release's two rules
(`accountOf_dropStep`, and `wellFormed_drop` for the discipline) and the binding of a
variable (`accountOf_bindVar` and `accountOf_appVar`), the latter under the binder's own
linearity --- the binder occurring once in the body, and the value's variable occurring
nowhere in it --- which the account relation does not itself supply and the theorems name.

**Where the account does not move with the term.** Three instructions move the account
*against* the term, and the module states each rather than assuming it away. A `dup`
*supplies* an occurrence: the term's free occurrences lose the instruction's own name
while the account gains the occurrence, so the account the rule leaves is one occurrence
above the body's own (`accountOf_dupStep`). The instructions that *consume a value* ---
`val x = v; e₂` with an allocated `v`, `(λx. body) v` with an allocated argument, and
`store` --- leave the value's own occurrences in the account while the result's free
occurrences have none of them, so the account the rule leaves is wider than the result's
own (`accountOf_storeStep`). `TStep` therefore does not preserve `WellFormed` in general:
it preserves it exactly where the rules move one occurrence with the term, which is what
the theorems above state, and the check module exhibits each instruction that does not.

**The composition.** With the two facts a session root satisfies by its shape --- no slot
of the heap and no handle the run holds names it (`Rooted`) --- a disciplined write at the
root of a coupled configuration takes the destructive branch with no further assumption
(`rooted_store_destructive`): the discipline supplies the two premises
`Ownership.store_owned_is_destructive` cannot derive, and the root's shape supplies the
two hypotheses that theorem names.

**What is modelled, and what is trusted.** The account is a logical reading of the
configuration, not a machine count: it lists the term's own occurrences as pairs, and its
reference reading is `expand`. The write's branch is `RCHeap.update`'s, as `Ownership`
states it, and nothing here is about compiled code.
-/
import Scidonia.RC.Ownership

namespace Scidonia.RC

open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap

/-! ## Reading a list of names through an environment

A list of names is read two ways: at the references the environment binds them to
(`refsOf`), and at the pairs of a name and its reference (`pairsOf`). A name the
environment binds nowhere contributes to neither. -/

/-- The references a list of names is read at, in order. -/
def refsOf (rho : TEnv) (us : List Var) : List Ref := us.filterMap (fun x => rho.lookup x)

/-- The pairs a list of names names, in order: one pair per name, the name and the
reference the environment binds it to. -/
def pairsOf (rho : TEnv) (us : List Var) : Multi :=
  us.filterMap (fun x => (rho.lookup x).map (fun r => (x, r)))

/-- The pairs the term's free occurrences name: the term's own occurrences, one pair per
occurrence, each occurrence's variable and the reference the environment binds it to. -/
def occsOf (rho : TEnv) (e : Expr) : Multi := pairsOf rho (uses e)

/-- A term's account is the pairs its free occurrences name: the two spellings are the
same list, which is what lets a statement about one be read at the other. -/
theorem occsOf_pairsOf (rho : TEnv) (e : Expr) : occsOf rho e = pairsOf rho (uses e) := rfl

/-- An empty list names nothing. -/
@[simp] theorem refsOf_nil (rho : TEnv) : refsOf rho [] = [] := rfl

/-- An empty list names no pair. -/
@[simp] theorem pairsOf_nil (rho : TEnv) : pairsOf rho [] = ([] : Multi) := rfl

/-- Reading a concatenation is reading each part. -/
theorem refsOf_append (rho : TEnv) (us vs : List Var) :
    refsOf rho (us ++ vs) = refsOf rho us ++ refsOf rho vs := by
  simp [refsOf, List.filterMap_append]

/-- Reading a concatenation at the pairs is reading each part at the pairs. -/
theorem pairsOf_append (rho : TEnv) (us vs : List Var) :
    pairsOf rho (us ++ vs) = pairsOf rho us ++ pairsOf rho vs := by
  simp [pairsOf, List.filterMap_append]

/-- A name the environment binds contributes its reference. -/
@[simp] theorem refsOf_cons_some {rho : TEnv} {x : Var} {r : Ref} (h : rho.lookup x = some r)
    (us : List Var) : refsOf rho (x :: us) = r :: refsOf rho us := by
  simp [refsOf, h]

/-- A name the environment binds contributes its pair. -/
@[simp] theorem pairsOf_cons_some {rho : TEnv} {x : Var} {r : Ref} (h : rho.lookup x = some r)
    (us : List Var) : pairsOf rho (x :: us) = (x, r) :: pairsOf rho us := by
  simp [pairsOf, h]

/-- A name the environment binds nowhere contributes nothing. -/
@[simp] theorem refsOf_cons_none {rho : TEnv} {x : Var} (h : rho.lookup x = none)
    (us : List Var) : refsOf rho (x :: us) = refsOf rho us := by
  simp [refsOf, h]

/-- A name the environment binds nowhere contributes no pair. -/
@[simp] theorem pairsOf_cons_none {rho : TEnv} {x : Var} (h : rho.lookup x = none)
    (us : List Var) : pairsOf rho (x :: us) = pairsOf rho us := by
  simp [pairsOf, h]

/-- A reference a list names is the reference its variable is bound to. -/
theorem mem_refsOf {rho : TEnv} {us : List Var} {r : Ref} (h : r ∈ refsOf rho us) :
    ∃ x ∈ us, rho.lookup x = some r := by
  rw [refsOf, List.mem_filterMap] at h
  obtain ⟨x, hx, hlook⟩ := h
  exact ⟨x, hx, hlook⟩

/-- A variable of a list the environment binds contributes its reference. -/
theorem mem_refsOf_of {rho : TEnv} {us : List Var} {x : Var} {r : Ref} (hx : x ∈ us)
    (h : rho.lookup x = some r) : r ∈ refsOf rho us := by
  rw [refsOf, List.mem_filterMap]
  exact ⟨x, hx, h⟩

/-- A pair a list names is a pair of a variable of the list and the reference the
environment binds it to. -/
theorem mem_pairsOf {rho : TEnv} {us : List Var} {p : Var × Ref}
    (h : p ∈ pairsOf rho us) : ∃ x ∈ us, rho.lookup x = some p.2 ∧ p.1 = x := by
  rw [pairsOf, List.mem_filterMap] at h
  obtain ⟨x, hx, hlook⟩ := h
  rw [Option.map_eq_some_iff] at hlook
  obtain ⟨r, hlook', hr⟩ := hlook
  exact ⟨x, hx, by rw [← hr]; exact hlook', (congrArg Prod.fst hr).symm⟩

/-! ## The account of a list of names, and of a term

The account of a term is the account of its free occurrences: the reference reading, the
pair reading, and the environment's own reading of the term's names. -/

/-- The account of a list of names in an environment: the references the account holds are
the ones the names are read at, the account's pairs are pairs of the names, and the
environment binds every name of the list. -/
def AcctOf (rho : TEnv) (us : List Var) (m : Multi) : Prop :=
  (∀ r, (expand m).count r = (refsOf rho us).count r)
    ∧ (∀ p : Var × Ref, m.count p ≤ (pairsOf rho us).count p)
    ∧ (∀ x ∈ us, ∃ r, rho.lookup x = some r)

/-- An account's references are the names it was handed, read at their variables. -/
theorem AcctOf.refs {rho : TEnv} {us : List Var} {m : Multi} (h : AcctOf rho us m) :
    ∀ r, (expand m).count r = (refsOf rho us).count r := h.1

/-- An account's pairs are pairs of the names it was handed. -/
theorem AcctOf.pairs {rho : TEnv} {us : List Var} {m : Multi} (h : AcctOf rho us m) :
    ∀ p : Var × Ref, m.count p ≤ (pairsOf rho us).count p := h.2.1

/-- The environment reads every name the account was handed. -/
theorem AcctOf.dom {rho : TEnv} {us : List Var} {m : Multi} (h : AcctOf rho us m) :
    ∀ x ∈ us, ∃ r, rho.lookup x = some r := h.2.2

/-- The account of a term in an environment, read at the term's own occurrences: the
account *is* the term's free occurrences, each read at the reference the environment binds
its variable to. The first conjunct is the reference reading `Ownership`'s store theorems
are stated about; the second is what makes a pair --- and not merely a count --- readable
out of the account, and implies that every pair the account holds names one of the term's
free variables at the reference the environment binds it to (`Bound`); the third is what
makes "read through the environment" mean something, and is the only clause that says the
environment binds the term's names at all. -/
def AccountOf (rho : TEnv) (e : Expr) (m : Multi) : Prop := AcctOf rho (uses e) m

/-- The account's references are the term's free occurrences read at their variables. -/
theorem AccountOf.refs {rho : TEnv} {e : Expr} {m : Multi} (h : AccountOf rho e m) :
    ∀ r, (expand m).count r = (refsOf rho (uses e)).count r := h.1

/-- The account's pairs are pairs the term's own occurrences name: the account holds no
occurrence the term does not have. -/
theorem AccountOf.pairs {rho : TEnv} {e : Expr} {m : Multi} (h : AccountOf rho e m) :
    ∀ p : Var × Ref, m.count p ≤ (occsOf rho e).count p := h.2.1

/-- The environment reads every free variable of the term. -/
theorem AccountOf.dom {rho : TEnv} {e : Expr} {m : Multi} (h : AccountOf rho e m) :
    ∀ x ∈ uses e, ∃ r, rho.lookup x = some r := h.2.2

/-- A pair of the account is the term's own occurrence read at its variable: its tag is a
free variable of the term and the environment binds that variable to the pair's
reference. The pair reading is what makes this readable. -/
theorem AccountOf.bound {rho : TEnv} {e : Expr} {m : Multi} (h : AccountOf rho e m) :
    Bound rho m := by
  intro p hp
  have hpos : 0 < m.count p := List.count_pos_iff.mpr hp
  have hle := h.pairs p
  have hmem : p ∈ occsOf rho e := List.count_pos_iff.mp (by omega)
  obtain ⟨x, hx, hlook, hfst⟩ := mem_pairsOf hmem
  rw [hfst]
  exact hlook

/-- The account's tags are the term's free variables. -/
theorem AccountOf.names {rho : TEnv} {e : Expr} {m : Multi} (h : AccountOf rho e m) :
    ∀ p ∈ m, p.1 ∈ uses e := by
  intro p hp
  have hpos : 0 < m.count p := List.count_pos_iff.mpr hp
  have hmem : p ∈ occsOf rho e := List.count_pos_iff.mp (by have := h.pairs p; omega)
  obtain ⟨x, hx, _, hfst⟩ := mem_pairsOf hmem
  rw [hfst]
  exact hx

/-- An account holds no pair the term's occurrences do not name, so a reference outside
the term's own references is counted zero. -/
theorem AccountOf.count_eq_zero {rho : TEnv} {e : Expr} {m : Multi} (h : AccountOf rho e m)
    {r : Ref} (hr : r ∉ refsOf rho (uses e)) : (expand m).count r = 0 := by
  rw [h.refs r]
  exact List.count_eq_zero.mpr hr

/-! ## The discipline -/

/-- Distinct free variables of the term name distinct references: the condition under
which "once in the term" means "once in the account", since without it two distinct names
bound to one reference would count twice. -/
def InjectiveOn (rho : TEnv) (e : Expr) : Prop :=
  ∀ x ∈ uses e, ∀ z ∈ uses e, rho.lookup x = rho.lookup z → x = z

/-- Every write in the term has a subject variable, and that variable occurs exactly once
among the term's free variables: a traverse of the term, one clause per constructor, in
the style of `uses`. A write whose subject is not a variable, and one whose subject's name
occurs more than once among the term's free occurrences, are not disciplined. -/
def WritesOwned : Expr → Prop
  | .var _ => True
  | .lam _ body => WritesOwned body
  | .app f a => WritesOwned f ∧ WritesOwned a
  | .bind _ e₁ e₂ => WritesOwned e₁ ∧ WritesOwned e₂
  | .matchC s _ _ body => WritesOwned s ∧ WritesOwned body
  | .dup _ e => WritesOwned e
  | .drop _ e => WritesOwned e
  | .con0 _ => True
  | .con1 _ a => WritesOwned a
  | .con2 _ a b => WritesOwned a ∧ WritesOwned b
  | .store s i v =>
      (match s with
        | .var y => (uses (.store (.var y) i v)).count y = 1
        | _ => False) ∧ WritesOwned v

/-- A write whose subject is a variable is disciplined exactly when that variable occurs
once among the write's free occurrences and the value is disciplined. -/
theorem writesOwned_store_var (y : Var) (i : Nat) (v : Expr) :
    WritesOwned (.store (.var y) i v)
      ↔ ((uses (.store (.var y) i v)).count y = 1 ∧ WritesOwned v) := by
  simp only [WritesOwned]

/-- The discipline: the account is the term's own references (`AccountOf`), distinct free
variables name distinct references (`InjectiveOn`), and every write's subject is a
variable occurring exactly once among the term's free variables (`WritesOwned`). -/
def WellFormed (rho : TEnv) (m : Multi) (e : Expr) : Prop :=
  AccountOf rho e m ∧ InjectiveOn rho e ∧ WritesOwned e

/-- A disciplined configuration's account is the term's own references. -/
theorem WellFormed.account {rho : TEnv} {m : Multi} {e : Expr} (h : WellFormed rho m e) :
    AccountOf rho e m := h.1

/-- A disciplined configuration's environment names distinct references for the term's
distinct free variables. -/
theorem WellFormed.injective {rho : TEnv} {m : Multi} {e : Expr} (h : WellFormed rho m e) :
    InjectiveOn rho e := h.2.1

/-- A disciplined configuration's term is a term every write of which has a subject
variable owned once. -/
theorem WellFormed.writes {rho : TEnv} {m : Multi} {e : Expr} (h : WellFormed rho m e) :
    WritesOwned e := h.2.2

/-! ## The account of a construct

The account of a term is read off its subterms: the leaves are the base cases, and a
compound term's account is its subterms' accounts glued the way the term's own
occurrences are glued. -/

/-- Prepending one reference to two lists whose counts agree keeps their counts
agreeing. -/
theorem count_cons_of_count_eq {r : Ref} {l l' : List Ref}
    (h : ∀ s, l.count s = l'.count s) (s : Ref) :
    (r :: l).count s = (r :: l').count s := by
  by_cases hs : s = r
  · subst hs
    rw [List.count_cons_self, List.count_cons_self, h s]
  · rw [List.count_cons_of_ne (b := r) (a := s) (fun hh => hs hh.symm),
      List.count_cons_of_ne (b := r) (a := s) (fun hh => hs hh.symm), h s]

/-- A pair a `dup` or a `drop` supplies is the first the list it builds holds. -/
@[simp] theorem count_insert_self (m : Multi) (y : Var) (r : Ref) :
    (Multi.insert m y r).count (y, r) = m.count (y, r) + 1 := by
  simp [Multi.insert]

/-- A pair another one is not is counted as the list it was built from counts it. -/
theorem count_insert_of_ne {m : Multi} {y : Var} {r : Ref} {p : Var × Ref}
    (h : p ≠ (y, r)) : (Multi.insert m y r).count p = m.count p :=
  List.count_cons_of_ne (b := (y, r)) (a := p) (fun hh => h hh.symm)

/-- The occurrence a `drop` consumes is the first pair equal to the pair the instruction
reads, so the account the rule leaves is the account the term held with that pair
removed. -/
theorem dropOcc_eq_erase (m : Multi) (y : Var) (r : Ref) :
    Multi.dropOcc m y r = m.erase (y, r) := by
  induction m with
  | nil => rfl
  | cons p t ih =>
      obtain ⟨x, s⟩ := p
      by_cases h : (x, s) = (y, r)
      · rw [show Multi.dropOcc ((x, s) :: t) y r = t from by simp [Multi.dropOcc, h]]
        rw [h, List.erase_cons_head]
      · rw [show Multi.dropOcc ((x, s) :: t) y r = (x, s) :: Multi.dropOcc t y r from by
          simp [Multi.dropOcc, h], ih]
        rw [List.erase_cons_tail (by simpa using h)]

/-- A `drop` removes exactly one pair: the count of the pair it reads falls by one and
every other pair's count is the one the account held. The condition is written with the
pair the instruction reads on the left, the orientation the list's own count lemmas
write. -/
theorem count_dropOcc (m : Multi) {y : Var} {r : Ref} (h : (y, r) ∈ m) (p : Var × Ref) :
    (Multi.dropOcc m y r).count p + (if (y, r) = p then 1 else 0) = m.count p := by
  rw [dropOcc_eq_erase]
  by_cases hp : (y, r) = p
  · have hm : p ∈ m := hp ▸ h
    rw [ite_eq_left hp, hp, List.count_erase_self]
    have hpos : 1 ≤ m.count p := List.count_pos_iff.mpr hm
    omega
  · rw [ite_eq_right hp, List.count_erase_of_ne (fun hh => hp hh.symm)]
    omega

/-- Reading a list at the environment that binds a name to a reference splits into reading
it at the old environment off that name, plus the name's own occurrences read at the new
reference. -/
theorem refsOf_set_count (rho : TEnv) (x : Var) (r : Ref) (us : List Var) (s : Ref) :
    (refsOf (TEnv.set rho x r) us).count s
      = (refsOf rho (us.filter (fun y => decide (y ≠ x)))).count s
        + (if r = s then us.count x else 0) := by
  induction us with
  | nil => simp [refsOf]
  | cons y t ih =>
      by_cases hy : y = x
      · have hf : (x :: t).filter (fun y' => decide (y' ≠ x))
            = t.filter (fun y' => decide (y' ≠ x)) := by simp
        rw [hy, hf, refsOf_cons_some (TEnv.lookup_set_self rho x r) t]
        by_cases hs : s = r
        · rw [ite_eq_left hs.symm] at ih ⊢
          rw [hs] at ih ⊢
          rw [List.count_cons_self, ih, List.count_cons_self]
          omega
        · rw [ite_eq_right (fun hh => hs hh.symm)] at ih ⊢
          rw [List.count_cons_of_ne (b := r) (a := s) (fun hh => hs hh.symm)]
          rw [ih]
      · have hf : (y :: t).filter (fun y' => decide (y' ≠ x))
            = y :: t.filter (fun y' => decide (y' ≠ x)) := by
          rw [List.filter_cons_of_pos (p := fun y' => decide (y' ≠ x)) (a := y) (l := t)]
          simp [hy]
        rw [hf, List.count_cons_of_ne (b := y) (a := x) hy]
        have hlook : (TEnv.set rho x r).lookup y = rho.lookup y :=
          TEnv.lookup_set_of_ne (x := x) (y := y) (fun hh => hy hh.symm) r
        cases hly : rho.lookup y with
        | none =>
            rw [refsOf_cons_none (by rw [hlook, hly]) t, refsOf_cons_none hly, ih]
        | some s' =>
            rw [refsOf_cons_some (by rw [hlook, hly]) t, refsOf_cons_some hly]
            by_cases hs : s = s'
            · rw [hs] at ih ⊢
              rw [List.count_cons_self, ih, List.count_cons_self]
              omega
            · rw [List.count_cons_of_ne (b := s') (a := s) (fun hh => hs hh.symm)]
              rw [List.count_cons_of_ne (b := s') (a := s) (fun hh => hs hh.symm)]
              rw [ih]

/-- Reading a list at the environment that binds a name to a reference splits at the
pairs the same way. -/
theorem pairsOf_set_count (rho : TEnv) (x : Var) (r : Ref) (us : List Var) (p : Var × Ref) :
    (pairsOf (TEnv.set rho x r) us).count p
      = (pairsOf rho (us.filter (fun y => decide (y ≠ x)))).count p
        + (if (x, r) = p then us.count x else 0) := by
  induction us with
  | nil => simp [pairsOf]
  | cons y t ih =>
      by_cases hy : y = x
      · have hf : (x :: t).filter (fun y' => decide (y' ≠ x))
            = t.filter (fun y' => decide (y' ≠ x)) := by simp
        rw [hy, hf, pairsOf_cons_some (TEnv.lookup_set_self rho x r) t]
        by_cases hp : p = (x, r)
        · rw [ite_eq_left hp.symm] at ih ⊢
          rw [hp] at ih ⊢
          rw [List.count_cons_self, ih, List.count_cons_self]
          omega
        · rw [ite_eq_right (fun hh => hp hh.symm)] at ih ⊢
          rw [List.count_cons_of_ne (b := (x, r)) (a := p) (fun hh => hp hh.symm), ih]
      · have hf : (y :: t).filter (fun y' => decide (y' ≠ x))
            = y :: t.filter (fun y' => decide (y' ≠ x)) := by
          rw [List.filter_cons_of_pos (p := fun y' => decide (y' ≠ x)) (a := y) (l := t)]
          simp [hy]
        rw [hf, List.count_cons_of_ne (b := y) (a := x) hy]
        have hlook : (TEnv.set rho x r).lookup y = rho.lookup y :=
          TEnv.lookup_set_of_ne (x := x) (y := y) (fun hh => hy hh.symm) r
        cases hly : rho.lookup y with
        | none =>
            rw [pairsOf_cons_none (by rw [hlook, hly]) t, pairsOf_cons_none hly, ih]
        | some s' =>
            rw [pairsOf_cons_some (by rw [hlook, hly]) t, pairsOf_cons_some hly]
            by_cases hp : p = (y, s')
            · rw [hp] at ih ⊢
              rw [List.count_cons_self, ih, List.count_cons_self]
              omega
            · rw [List.count_cons_of_ne (b := (y, s')) (a := p) (fun hh => hp hh.symm)]
              rw [List.count_cons_of_ne (b := (y, s')) (a := p) (fun hh => hp hh.symm)]
              rw [ih]

/-- The account of a list is its two readings: the account of a concatenation is the sum
of the accounts. -/
theorem acctOf_append {rho : TEnv} {us vs : List Var} {m₁ m₂ : Multi}
    (h₁ : AcctOf rho us m₁) (h₂ : AcctOf rho vs m₂) :
    AcctOf rho (us ++ vs) (m₁ ++ m₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    rw [show expand (m₁ ++ m₂) = expand m₁ ++ expand m₂ from List.map_append,
      List.count_append, refsOf_append, List.count_append, h₁.1 r, h₂.1 r]
  · intro p
    rw [List.count_append, pairsOf_append, List.count_append]
    exact Nat.add_le_add (h₁.2.1 p) (h₂.2.1 p)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h₁.2.2 x hx
    · exact h₂.2.2 x hx

/-- The account of a variable is the pair of its name and the reference its environment
binding reads. -/
theorem accountOf_var {rho : TEnv} {x : Var} {r : Ref} (h : rho.lookup x = some r) :
    AccountOf rho (.var x) [(x, r)] := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    simp only [uses, refsOf_cons_some h, refsOf_nil]
    simp
  · intro p
    simp only [uses, pairsOf_cons_some h, pairsOf_nil]
    exact Nat.le_refl _
  · intro x' hx'
    rw [show uses (.var x) = [x] from rfl, List.mem_singleton] at hx'
    subst hx'
    exact ⟨r, h⟩

/-- The account of a nullary node is empty: it has no free occurrence. -/
theorem accountOf_con0 (rho : TEnv) (c : Ctor) : AccountOf rho (.con0 c) [] := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    rw [show uses (.con0 c) = [] from rfl, refsOf_nil,
      show expand ([] : Multi) = [] from rfl]
  · intro p
    rw [show uses (.con0 c) = [] from rfl, pairsOf_nil]
    exact Nat.le_refl _
  · intro x hx
    rw [show uses (.con0 c) = [] from rfl] at hx
    simp at hx

/-- A term with no free occurrence has the empty account. -/
theorem accountOf_of_closed {rho : TEnv} {e : Expr} (h : uses e = []) :
    AccountOf rho e [] := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    rw [h, refsOf_nil, show expand ([] : Multi) = [] from rfl]
  · intro p
    rw [h, pairsOf_nil]
    exact Nat.le_refl _
  · intro x hx
    rw [h] at hx
    simp at hx

/-- The account of an application is the accounts of its two subterms summed. -/
theorem accountOf_app {rho : TEnv} {f a : Expr} {m₁ m₂ : Multi}
    (h₁ : AccountOf rho f m₁) (h₂ : AccountOf rho a m₂) :
    AccountOf rho (.app f a) (m₁ ++ m₂) :=
  acctOf_append h₁ h₂

/-- The account of a unary node is its field's account. -/
theorem accountOf_con1 {rho : TEnv} {c : Ctor} {a : Expr} {m : Multi}
    (h : AccountOf rho a m) : AccountOf rho (.con1 c a) m :=
  h

/-- The account of a binary node is the accounts of its two fields summed. -/
theorem accountOf_con2 {rho : TEnv} {ct : Ctor} {a b : Expr} {m₁ m₂ : Multi}
    (h₁ : AccountOf rho a m₁) (h₂ : AccountOf rho b m₂) :
    AccountOf rho (.con2 ct a b) (m₁ ++ m₂) :=
  acctOf_append h₁ h₂

/-- The account of a write is the accounts of its subject and its value summed. -/
theorem accountOf_store {rho : TEnv} {s : Expr} {i : Nat} {v : Expr} {m₁ m₂ : Multi}
    (h₁ : AccountOf rho s m₁) (h₂ : AccountOf rho v m₂) :
    AccountOf rho (.store s i v) (m₁ ++ m₂) :=
  acctOf_append h₁ h₂

/-- The pairs a `dup` node's free occurrences name: the occurrence the instruction
supplies and its body's. -/
theorem occsOf_dup {rho : TEnv} {y : Var} {r : Ref} {e : Expr} (h : rho.lookup y = some r) :
    occsOf rho (.dup y e) = (y, r) :: occsOf rho e := by
  change pairsOf rho (y :: uses e) = (y, r) :: pairsOf rho (uses e)
  rw [pairsOf_cons_some h]

/-- The pairs a `drop` node's free occurrences name: the occurrence the instruction
releases and its body's. -/
theorem occsOf_drop {rho : TEnv} {y : Var} {r : Ref} {e : Expr} (h : rho.lookup y = some r) :
    occsOf rho (.drop y e) = (y, r) :: occsOf rho e := by
  change pairsOf rho (y :: uses e) = (y, r) :: pairsOf rho (uses e)
  rw [pairsOf_cons_some h]

/-- The account of a `dup` is the account of its body with the occurrence the instruction
supplies: the term holds one occurrence more than its body does. -/
theorem accountOf_dup {rho : TEnv} {e : Expr} {m : Multi} {y : Var} {r : Ref}
    (h : AccountOf rho e m) (hlook : rho.lookup y = some r) :
    AccountOf rho (.dup y e) (Multi.insert m y r) := by
  change AcctOf rho (y :: uses e) (Multi.insert m y r)
  refine ⟨?_, ?_, ?_⟩
  · intro s
    rw [expand_insert, refsOf_cons_some hlook]
    exact count_cons_of_count_eq (fun s => h.refs s) s
  · intro p
    have hp := h.pairs p
    rw [pairsOf_cons_some hlook, ← occsOf_pairsOf]
    by_cases heq : p = (y, r)
    · rw [heq] at hp ⊢
      rw [count_insert_self, List.count_cons_self]
      omega
    · rw [count_insert_of_ne heq,
        List.count_cons_of_ne (b := (y, r)) (a := p) (fun hh => heq hh.symm)]
      exact hp
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨r, hlook⟩
    · exact h.dom x hx

/-- The account of a `drop` is the account of its body with the occurrence the instruction
releases: the term holds the occurrence its body's release reads. -/
theorem accountOf_drop {rho : TEnv} {e : Expr} {m : Multi} {y : Var} {r : Ref}
    (h : AccountOf rho e m) (hlook : rho.lookup y = some r) :
    AccountOf rho (.drop y e) (Multi.insert m y r) :=
  accountOf_dup h hlook

/-! ## The moves the runtime's rules make

The runtime's own rules move the account where they move one occurrence with the term: the
release's rules, and the binding of a variable. The instructions that supply an occurrence
or consume a value move the account *against* the term, and each of those is stated too. -/

/-- The release's move: the account of a release is the account of its body with the
released occurrence, so the body's account is the release's with that occurrence removed.
This is the move both of `Target.TStep`'s release rules make, and it needs nothing of the
heap but the pair the instruction reads. -/
theorem accountOf_dropStep {rho : TEnv} {m : Multi} {y : Var} {r : Ref} {e : Expr}
    (hacc : AccountOf rho (.drop y e) m) (hlook : rho.lookup y = some r)
    (hsub : (y, r) ∈ m) : AccountOf rho e (Multi.dropOcc m y r) := by
  change AcctOf rho (uses e) (Multi.dropOcc m y r)
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have h1 := hacc.refs s
    change (expand m).count s = (refsOf rho (y :: uses e)).count s at h1
    rw [refsOf_cons_some hlook] at h1
    by_cases hs : s = r
    · rw [hs] at h1 ⊢
      rw [List.count_cons_self] at h1
      have hself := expand_dropOcc_count_self m y hsub
      omega
    · rw [List.count_cons_of_ne (b := r) (a := s) (fun hh => hs hh.symm)] at h1
      have hne := expand_dropOcc_count_of_ne m y (r := r) (s := s) hs
      omega
  · intro p
    have hp := hacc.pairs p
    rw [show occsOf rho (.drop y e) = pairsOf rho (uses (.drop y e)) from rfl,
      show uses (.drop y e) = y :: uses e from rfl, pairsOf_cons_some hlook,
      ← occsOf_pairsOf] at hp
    rw [List.count_cons] at hp
    simp only [beq_iff_eq] at hp
    rw [← occsOf_pairsOf]
    have hdrop := count_dropOcc m hsub p
    by_cases heq : (y, r) = p
    · rw [ite_eq_left heq] at hp hdrop
      omega
    · rw [ite_eq_right heq] at hp hdrop
      omega
  · intro x hx
    exact hacc.dom x (List.mem_cons_of_mem _ hx)

/-- The move the binding of a variable makes: the account of a term whose instruction reads
a value's variable moves to the body's account with the value's occurrence replaced by the
binder's, once the binder occurs exactly once in the body. The two readings of the
instruction's own account are the hypotheses; the value's variable being read at the
reference the account holds for it is what the pair hypothesis reads, so it is not a
hypothesis of its own. -/
theorem acctOf_bindVar {rho : TEnv} {us us' : List Var} {m : Multi} {x z : Var} {r : Ref}
    (hacc : AcctOf rho us' m) (hsub : (z, r) ∈ m)
    (hreads : ∀ s, (refsOf rho us').count s
      = (refsOf rho (us.filter (fun y => decide (y ≠ x)))).count s + (if r = s then 1 else 0))
    (hpairs : ∀ p, (pairsOf rho us').count p
      = (pairsOf rho (us.filter (fun y => decide (y ≠ x)))).count p
        + (if (z, r) = p then 1 else 0))
    (hbound : ∀ y ∈ us, y ≠ x → ∃ s, rho.lookup y = some s)
    (hlinear : us.count x = 1) :
    AcctOf (TEnv.set rho x r) us (Multi.insert (Multi.dropOcc m z r) x r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have h1 := hacc.refs s
    rw [hreads s] at h1
    rw [refsOf_set_count rho x r us s]
    rw [expand_insert]
    by_cases hs : s = r
    · rw [hs] at h1 ⊢
      rw [ite_eq_left rfl] at h1
      rw [List.count_cons_self, ite_eq_left rfl, hlinear]
      have hself := expand_dropOcc_count_self m z hsub
      omega
    · rw [ite_eq_right (fun hh => hs hh.symm)] at h1
      rw [List.count_cons_of_ne (b := r) (a := s) (fun hh => hs hh.symm),
        ite_eq_right (fun hh => hs hh.symm)]
      have hne := expand_dropOcc_count_of_ne m z (r := r) (s := s) hs
      omega
  · intro p
    have hp := hacc.pairs p
    rw [hpairs p] at hp
    rw [pairsOf_set_count rho x r us p, hlinear]
    have hdrop := count_dropOcc m hsub p
    by_cases hx : p = (x, r)
    · rw [hx] at hp hdrop ⊢
      rw [count_insert_self, ite_eq_left rfl]
      omega
    · rw [ite_eq_right (fun hh => hx hh.symm)]
      rw [count_insert_of_ne hx]
      omega
  · intro y hy
    by_cases hyx : y = x
    · rw [hyx]
      exact ⟨r, TEnv.lookup_set_self rho x r⟩
    · rw [TEnv.lookup_set_of_ne (fun hh => hyx hh.symm) r]
      exact hbound y hy hyx

/-- The move a binding of a variable makes, at the configuration's own account. -/
theorem accountOf_bindVar {rho : TEnv} {m : Multi} {x z : Var} {r : Ref} {e₂ : Expr}
    (hacc : AccountOf rho (.bind x (.var z) e₂) m) (hlook : rho.lookup z = some r)
    (hsub : (z, r) ∈ m) (hlinear : (uses e₂).count x = 1) :
    AccountOf (TEnv.set rho x r) e₂ (Multi.insert (Multi.dropOcc m z r) x r) := by
  refine acctOf_bindVar hacc hsub ?_ ?_ ?_ hlinear
  · intro s
    rw [show uses (.bind x (.var z) e₂) = [z] ++ (uses e₂).filter (fun y => y ≠ x) from rfl,
      refsOf_append, refsOf_cons_some hlook, refsOf_nil, List.count_append]
    by_cases hs : s = r
    · rw [hs] at ⊢
      rw [List.count_cons_self, List.count_nil, ite_eq_left rfl]
      try omega
    · rw [List.count_cons_of_ne (b := r) (a := s) (fun hh => hs hh.symm), List.count_nil,
        ite_eq_right (fun hh => hs hh.symm)]
      try omega
  · intro p
    rw [show uses (.bind x (.var z) e₂) = [z] ++ (uses e₂).filter (fun y => y ≠ x) from rfl,
      pairsOf_append, pairsOf_cons_some hlook, pairsOf_nil, List.count_append]
    by_cases hp : p = (z, r)
    · rw [hp] at ⊢
      rw [List.count_cons_self, List.count_nil, ite_eq_left rfl]
      try omega
    · rw [List.count_cons_of_ne (b := (z, r)) (a := p) (fun hh => hp hh.symm), List.count_nil,
        ite_eq_right (fun hh => hp hh.symm)]
      try omega
  · intro y hy hyx
    exact hacc.dom y (List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hyx⟩))

/-- The move an application to a variable makes, at the configuration's own account. -/
theorem accountOf_appVar {rho : TEnv} {m : Multi} {x z : Var} {r : Ref} {body : Expr}
    (hacc : AccountOf rho (.app (.lam x body) (.var z)) m) (hlook : rho.lookup z = some r)
    (hsub : (z, r) ∈ m) (hlinear : (uses body).count x = 1) :
    AccountOf (TEnv.set rho x r) body (Multi.insert (Multi.dropOcc m z r) x r) := by
  refine acctOf_bindVar hacc hsub ?_ ?_ ?_ hlinear
  · intro s
    rw [show uses (.app (.lam x body) (.var z))
        = (uses body).filter (fun y => y ≠ x) ++ [z] from rfl,
      refsOf_append, refsOf_cons_some hlook, refsOf_nil, List.count_append]
    by_cases hs : s = r
    · rw [hs] at ⊢
      rw [List.count_cons_self, List.count_nil, ite_eq_left rfl]
      try omega
    · rw [List.count_cons_of_ne (b := r) (a := s) (fun hh => hs hh.symm), List.count_nil,
        ite_eq_right (fun hh => hs hh.symm)]
      try omega
  · intro p
    rw [show uses (.app (.lam x body) (.var z))
        = (uses body).filter (fun y => y ≠ x) ++ [z] from rfl,
      pairsOf_append, pairsOf_cons_some hlook, pairsOf_nil, List.count_append]
    by_cases hp : p = (z, r)
    · rw [hp] at ⊢
      rw [List.count_cons_self, List.count_nil, ite_eq_left rfl]
      try omega
    · rw [List.count_cons_of_ne (b := (z, r)) (a := p) (fun hh => hp hh.symm), List.count_nil,
        ite_eq_right (fun hh => hp hh.symm)]
      try omega
  · intro y hy hyx
    exact hacc.dom y (List.mem_append_left _
      (List.mem_filter.mpr ⟨hy, by simpa using hyx⟩))

/-- The `dup` rule's move is not the account's: the rule *supplies* an occurrence, so the
account it leaves is the body's own account with the supplied occurrence still on it, and
the body's account is the rule's with that occurrence removed. The account of the body is
therefore one occurrence above what the rule leaves, which is why no `TStep` of this shape
preserves the discipline. -/
theorem accountOf_dupStep {rho : TEnv} {m : Multi} {y : Var} {r : Ref} {e : Expr}
    (hacc : AccountOf rho e m) (_hlook : rho.lookup y = some r) :
    AccountOf rho e (Multi.dropOcc (Multi.insert m y r) y r)
      ∧ ¬ AccountOf rho e (Multi.insert m y r) := by
  have hdrop : Multi.dropOcc (Multi.insert m y r) y r = m := by
    simp [Multi.insert, Multi.dropOcc]
  refine ⟨by rw [hdrop]; exact hacc, ?_⟩
  intro h
  have h1 := h.refs r
  have h2 := hacc.refs r
  rw [expand_insert, List.count_cons_self] at h1
  omega

/-- The store's move is not the account's: an occurrence of the value's variable is a pair
the account holds --- read off the account's own reference count, with the injectivity of
the environment's reading making its variable the occurrence's --- and the result `.var y`'s
own account holds no pair but one of the subject's, so the account the rule leaves is wider
than the result's own. -/
theorem accountOf_storeStep {rho : TEnv} {m : Multi} {y : Var} {i : Nat} {v : Expr}
    (hacc : AccountOf rho (.store (.var y) i v) m) (hinj : InjectiveOn rho (.store (.var y) i v))
    {z : Var} {s : Ref} (hz : z ∈ uses v) (hzr : rho.lookup z = some s) (hzy : z ≠ y) :
    ¬ AccountOf rho (.var y) m := by
  intro h
  have hz' : z ∈ uses (.store (.var y) i v) := List.mem_append_right _ hz
  have hmem : s ∈ refsOf rho (uses (.store (.var y) i v)) := mem_refsOf_of hz' hzr
  have hpos : 0 < (expand m).count s := by
    rw [hacc.refs s]
    exact List.count_pos_iff.mpr hmem
  obtain ⟨p, hp, hps⟩ : ∃ p ∈ m, p.2 = s := by
    rw [expand, List.count_pos_iff, List.mem_map] at hpos
    exact hpos
  have hpz : p.1 = z :=
    hinj p.1 (hacc.names p hp) z hz' (by rw [hacc.bound p hp, hps, hzr])
  have hzn : (z, s) ∈ m := by rw [← hpz, ← hps]; exact hp
  have hbound := h.pairs (z, s)
  have hzero : (occsOf rho (.var y)).count (z, s) = 0 := by
    rw [List.count_eq_zero]
    intro hmem'
    obtain ⟨x, hx, _, hfst⟩ := mem_pairsOf hmem'
    rw [show uses (.var y) = [y] from rfl, List.mem_singleton] at hx
    exact hzy (hfst.trans hx)
  have hpos' : 0 < m.count (z, s) := List.count_pos_iff.mpr hzn
  omega

/-! ## The discipline survives the moves the account makes -/

/-- Binding a name to a value's reference keeps the environment injective on the body once
the value's variable is not free in the body: the body's names are read by the old
environment, and the new name reads the one reference, which no name of the body reads. -/
theorem injectiveOn_set {rho : TEnv} {us us' : List Var} {x z : Var} {r : Ref}
    (h : ∀ a ∈ us, ∀ b ∈ us, rho.lookup a = rho.lookup b → a = b)
    (hz : z ∈ us) (hlook : rho.lookup z = some r)
    (hsub : ∀ a ∈ us', a ≠ x → a ∈ us) (hzout : z ∉ us') :
    ∀ a ∈ us', ∀ b ∈ us', (TEnv.set rho x r).lookup a = (TEnv.set rho x r).lookup b → a = b := by
  intro a ha b hb hab
  by_cases hax : a = x
  · rw [hax, TEnv.lookup_set_self] at hab
    by_cases hbx : b = x
    · rw [hax, hbx]
    · exfalso
      rw [TEnv.lookup_set_of_ne (fun hh => hbx hh.symm) r] at hab
      have hbz : b = z := h b (hsub b hb hbx) z hz (by rw [← hab, hlook])
      exact hzout (hbz ▸ hb)
  · rw [TEnv.lookup_set_of_ne (fun hh => hax hh.symm) r] at hab
    by_cases hbx : b = x
    · exfalso
      rw [hbx] at hab
      rw [TEnv.lookup_set_self] at hab
      have haz : a = z := h a (hsub a ha hax) z hz (by rw [hab, hlook])
      exact hzout (haz ▸ ha)
    · rw [TEnv.lookup_set_of_ne (fun hh => hbx hh.symm) r] at hab
      exact h a (hsub a ha hax) b (hsub b hb hbx) hab

/-- The discipline survives a release: the account moves as the term does and the
environment and the term's body are what they were. `Target.TStep`'s two release rules make
exactly this move. -/
theorem wellFormed_drop {rho : TEnv} {m : Multi} {y : Var} {r : Ref} {e : Expr}
    (hw : WellFormed rho m (.drop y e)) (hlook : rho.lookup y = some r)
    (hsub : (y, r) ∈ m) : WellFormed rho (Multi.dropOcc m y r) e :=
  ⟨accountOf_dropStep hw.account hlook hsub,
    fun a ha b hb => hw.injective a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb),
    hw.writes⟩

/-- The discipline survives the release of a cell a second reference also names, the rule
`Target.TStep.dropShared`: its premises are the reference the subject names (which is the
lookup `wellFormed_drop` reads), the count of two or more the rule branches on, and the
occurrence the term holds, and the configuration it leaves is the release's. -/
theorem wellFormed_dropShared {c : CHeap} {rho : TEnv} {m : Multi} {y : Var} {r : Ref}
    {e : Expr} (hlook : rho.lookup y = some r) (_h2 : 2 ≤ CHeap.count c r)
    (hsub : (y, r) ∈ m) (hw : WellFormed rho m (.drop y e)) :
    WellFormed rho (Multi.dropOcc m y r) e :=
  wellFormed_drop hw hlook hsub

/-- The discipline survives the final release of a cell, the rule `Target.TStep.dropFinal`:
its premises are the reference the subject names, the count of one the rule branches on,
and the occurrence the term holds, and the configuration it leaves is the release's. -/
theorem wellFormed_dropFinal {c : CHeap} {rho : TEnv} {m : Multi} {y : Var} {r : Ref}
    {e : Expr} (hlook : rho.lookup y = some r) (_h1 : CHeap.count c r = 1)
    (hsub : (y, r) ∈ m) (hw : WellFormed rho m (.drop y e)) :
    WellFormed rho (Multi.dropOcc m y r) e :=
  wellFormed_drop hw hlook hsub

/-- The discipline survives the binding of a variable — `Target.TStep.bindVar` and
`Target.TStep.appVar` make this move — once the binder occurs exactly once in the body and
the value's variable is not free in it. Those two hypotheses are the binder's own linearity:
the account relation does not supply them, and the move is not preserved without them. -/
theorem wellFormed_bindVar {rho : TEnv} {m : Multi} {x z : Var} {r : Ref} {e₂ : Expr}
    (hw : WellFormed rho m (.bind x (.var z) e₂)) (hlook : rho.lookup z = some r)
    (hsub : (z, r) ∈ m) (hlinear : (uses e₂).count x = 1) (hz : z ∉ uses e₂) :
    WellFormed (TEnv.set rho x r) (Multi.insert (Multi.dropOcc m z r) x r) e₂ :=
  ⟨accountOf_bindVar hw.account hlook hsub hlinear,
    injectiveOn_set (us := uses (.bind x (.var z) e₂)) (us' := uses e₂)
      hw.injective (List.mem_cons_self ..) hlook
      (fun a ha hax => List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨ha, by simpa using hax⟩))
      hz,
    hw.writes.2⟩

/-- The discipline survives the binding of a variable in an application —
`Target.TStep.appVar` — under the same two linearity hypotheses. -/
theorem wellFormed_appVar {rho : TEnv} {m : Multi} {x z : Var} {r : Ref} {body : Expr}
    (hw : WellFormed rho m (.app (.lam x body) (.var z))) (hlook : rho.lookup z = some r)
    (hsub : (z, r) ∈ m) (hlinear : (uses body).count x = 1) (hz : z ∉ uses body) :
    WellFormed (TEnv.set rho x r) (Multi.insert (Multi.dropOcc m z r) x r) body :=
  ⟨accountOf_appVar hw.account hlook hsub hlinear,
    injectiveOn_set (us := uses (.app (.lam x body) (.var z))) (us' := uses body)
      hw.injective (List.mem_append_right _ (List.mem_singleton_self z)) hlook
      (fun a ha hax => List.mem_append_left _ (List.mem_filter.mpr ⟨ha, by simpa using hax⟩))
      hz,
    hw.writes.left⟩

/-! ## The discipline implies the store's hypotheses -/

/-- The discipline gives ownership at a write: the term's own account holds the subject's
occurrence, and — with the environment injective on the term's free variables — the account
counts the subject's reference once, because the write clause says the subject is the only
free occurrence of its name. This is where the discipline becomes the ownership
`Ownership.store_owned_is_destructive` consumes: its `hown` and `hm` are the two
conclusions here, and the third hypothesis of that theorem (the accounted cell's count) is
the subject's occurrence read at the account. -/
theorem wellFormed_store {rho : TEnv} {m : Multi} {y : Var} {i : Nat} {v : Expr}
    (h : WellFormed rho m (.store (.var y) i v)) :
    Owns rho m (.store (.var y) i v) ∧ ∃ r, rho.lookup y = some r ∧ (expand m).count r = 1 := by
  obtain ⟨hacc, hinj, hw⟩ := h
  have hw' := (writesOwned_store_var y i v).mp hw
  have hy : y ∈ uses (.store (.var y) i v) := List.mem_append_left _ (List.mem_singleton_self y)
  obtain ⟨r, hr⟩ := hacc.dom y hy
  have hyv : y ∉ uses v := by
    intro hmem
    have h1 : (uses (.store (.var y) i v)).count y = (uses v).count y + 1 := by
      rw [show uses (.store (.var y) i v) = [y] ++ uses v from rfl, List.count_append,
        List.count_singleton_self]
      omega
    have h2 : 1 ≤ (uses v).count y := List.count_pos_iff.mpr hmem
    omega
  have hzero : (refsOf rho (uses v)).count r = 0 := by
    rw [List.count_eq_zero]
    intro hmem
    obtain ⟨z, hz, hzr⟩ := mem_refsOf hmem
    have hzy : z = y :=
      hinj z (List.mem_append_right _ hz) y hy (by rw [hzr, hr])
    exact hyv (hzy ▸ hz)
  have hcount : (expand m).count r = 1 := by
    rw [hacc.refs r, show uses (.store (.var y) i v) = [y] ++ uses v from rfl,
      refsOf_append, refsOf_cons_some hr, refsOf_nil, List.count_append, hzero]
    simp
  obtain ⟨p, hp, hpr⟩ : ∃ p ∈ m, p.2 = r := by
    have hpos : 0 < (expand m).count r := by omega
    rw [expand, List.count_pos_iff, List.mem_map] at hpos
    obtain ⟨p, hp, hpr⟩ := hpos
    exact ⟨p, hp, hpr⟩
  have hpy : p = (y, r) := by
    have hb := hacc.bound p hp
    have hn := hacc.names p hp
    have hxy : p.1 = y := hinj p.1 hn y hy (by rw [hb, hpr, hr])
    exact Prod.ext hxy hpr
  exact ⟨Owns.store hr (by rw [← hpy]; exact hp), r, hr, hcount⟩

/-! ## The root of a session

A root is the reference a session's object is named by: no slot of the heap names it and
no handle the run holds names it. Those are the two facts a rooted configuration has by
its shape, and they are the two premises `Ownership.store_owned_is_destructive` names as
the ones the account cannot supply. -/

/-- A root: a reference no slot of the heap names and no handle the run holds names. -/
def Rooted (c : CHeap) (hs : List Ref) (r : Ref) : Prop := r ∉ CHeap.slots c ∧ r ∉ hs

/-- A root is not a reference any slot of the heap names, so the heap's slots count it
zero. -/
theorem Rooted.slot_count {c : CHeap} {hs : List Ref} {r : Ref} (h : Rooted c hs r) :
    (CHeap.slots c).count r = 0 :=
  List.count_eq_zero.mpr h.1

/-- A root is not a reference any handle the run holds names, so the handles count it
zero. -/
theorem Rooted.handle_count {c : CHeap} {hs : List Ref} {r : Ref} (h : Rooted c hs r) :
    hs.count r = 0 :=
  List.count_eq_zero.mpr h.2

/-- A reference no slot of the heap names is counted zero by the heap's slots: the shape a
heap has at a root it does not name. -/
theorem slot_count_zero_of_not_mem {c : CHeap} {r : Ref} (h : r ∉ CHeap.slots c) :
    (CHeap.slots c).count r = 0 :=
  List.count_eq_zero.mpr h

/-- A reference no handle names is counted zero by the handles: the shape `hs = []` and
the runner's own handle list have at a root they do not name. -/
theorem handle_count_zero_of_not_mem {hs : List Ref} {r : Ref} (h : r ∉ hs) :
    hs.count r = 0 :=
  List.count_eq_zero.mpr h

/-- The handles a root starts with are empty, and an empty list counts every reference
zero. -/
@[simp] theorem handle_count_zero_nil (r : Ref) : ([] : List Ref).count r = 0 := rfl

/-! ## The composition -/

/-- A disciplined write at the root of a coupled configuration is destructive. The
discipline supplies the two premises `Ownership.store_owned_is_destructive` cannot derive
--- the term's own occurrence of the subject and the account's counting it once --- and the
root's shape supplies the two hypotheses that theorem names, no slot of the heap and no
handle the run holding naming the cell (`Rooted`). What is left is the write rule's own
check on the written slots (`hks`, `writeCheck`'s third conjunct): it is the rule's premise
and not the discipline's, and it is named here rather than assumed silently. -/
theorem rooted_store_destructive {c : CHeap} {hs : List Ref} {rho : TEnv} {m : Multi}
    {y : Var} {r : Ref} {i : Nat} {v : Expr} {ks : List Ref}
    (hc : Couple c hs rho m) (hlook : rho.lookup y = some r)
    (hw : WellFormed rho m (.store (.var y) i v)) (hroot : Rooted c hs r) (hks : r ∉ ks) :
    (update c (hs ++ expand m) r ks).1.lookup r = some ks := by
  obtain ⟨hown, r', hr', hcount⟩ := wellFormed_store hw
  have hrr : r' = r := Option.some.inj (hr'.symm.trans hlook)
  exact store_owned_is_destructive hc hlook hown (hrr ▸ hcount) (Rooted.slot_count hroot)
    (Rooted.handle_count hroot) hks

end Scidonia.RC
