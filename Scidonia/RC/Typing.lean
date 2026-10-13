/-
The typing of the source: the discipline a λPure term has to be in for its writes to
be expressible on a reference-counted target.

`Scidonia.RC.Lower` gives the source a canonical lowering and states the environment
discipline it walks: a *borrowed* environment `Δ` the term may use freely and an
*owned* environment `Γ` it must consume, split at every construct by `claimEnv`,
`bindEnv`, `armEnv`, `forget` and `forgetAll`. That discipline is a *lowering*'s: it
says which target a term becomes, and its `var` clause is membership in `Δ` or `Γ`,
so it admits a term that uses an owned name more than once, the extra uses being
supplied by the `dup` instructions the `wrap` prologue emits. This module reads the
same discipline as a *typing*: `Typed Δ Γ e` is the same clauses over the same
canonical splits, with one rule per construct of the source and no target term, and
with the write's clause strengthened to what a destructive write needs.

**The write's clause.** A write's rule is the only place where multiplicity and not
membership is read. It requires the subject's variable to be owned exactly once in
the environment of the store (`Γ.count y = 1`) and not borrowed (`y ∉ Δ`): the write
is expressible only where the cell is the term's own, which is what a destructive
write on a cell of reference count one needs. The unrepresentability results below are
that clause's own inversion: a program whose write's subject is also used has no
derivation at the empty environments a closed program is read at, which is the
repository's form of "unwritable".

**The typing is the lowering's discipline, not a second one.** `typed_lowers` reads a
typing as a lowering: every typed term is a term the canonical strategy lowers from the
same environments. The splits are the module's own `claimEnv`, `bindEnv`, `armEnv`,
`forget` and `forgetAll` --- imported, not re-derived --- so the typing is the
lowering's environment discipline restricted to written subjects that are owned once,
and not a parallel notion.

## What is proved

* `typed_write_owned`: every write in a typed term has, at the environment the typing
  assigns its position, a subject owned exactly once there and not borrowed; stated as
  the recursive reading `WriteOwned`, which a traversal of the term carries.
* `dupValue_no_typing` and `dupArm_no_typing`: a program whose write's subject is also
  the written value, and one whose arm binds the subject twice, have no typing at the
  empty environments; `ownedValue_typed` and `ownedArm_typed` are the same shapes with
  the subject used once, typed.
* `typed_lowers`: a typed term is a term `Scidonia.RC.Lower` lowers from the same
  environments.
* `typed_pure`, `typed_step_pure` and `typed_run_pure`: a typed term is of the source
  fragment and stays in it along any run --- the half of survival the judgement's own
  clauses give.

## What is modelled, and what is trusted

The judgement is static, over the source's syntax and the two environments, with no
heap, no account and no target term: it says which source terms are written to reach a
reference-counted target. The environments are read as multisets in list form, exactly
as `Scidonia.RC.Lower` reads them, and the write's `Γ.count y = 1` is the multiset
count of the subject's name. Nothing here is about a compiled program; the target and
its runtime are `Scidonia.RC.Target`'s, and what the typing says about them is read
through the lowering.

**The typing is not preserved by every step at the environments the step starts from.**
A write's subject is exactly the place where a step's own environments stop describing
the term, because the redex consumes an occurrence the environments do not remove: the
redex `(λ0. store (var 0) 0 (var 5)) (var 5)` is typed at `[]`, `[5, 5]`, its write's
clause met at the body's `[0, 5]` and the argument's at `[5, 5]`, and its contractum
`store (var 5) 0 (var 5)` is typed at `[]`, `[5]` and not at `[]`, `[5, 5]` ---
substituting the variable `5` for the binder puts its occurrences where the binder's one
occurrence was, and the environment's two then fail the write's clause. The value
restriction a substitution semantics needs for that half is therefore about the
environment and not about the contractum's shape: the substituted term must be a
variable that is linear in the environment and not borrowed (`Γ.count y = 1`, `y ∉ Δ`).
Carrying that restriction through the reduction needs the environments of two
derivations to be compared --- a position's environment is a `filter` of its parent's, so
two derivations agree exactly where the term's usages agree --- and that comparison is
not built here; the section below states the obstruction and
`ScidoniaTest/Typing`'s `redex_typed`, `contractum_not_typed` and `contractum_typed_one`
are the witness.
-/
import Scidonia.RC.Lower
import Scidonia.RC.Pure

namespace Scidonia.RC

/-! ## The typing

One rule per construct of the source, each over the canonical splits of
`Scidonia.RC.Lower`, with the write's clause strengthened to ownership. -/

/-- The source term `e` is typed under the borrowed occurrences `Δ` and the owned
occurrences `Γ`: the lowering's environment discipline read as a typing, with a write's
subject required to be owned exactly once in its environment and not borrowed. The
environment is an index of the judgement and not a parameter of the rule's conclusion,
because a binder's body is typed at the environment the binder leaves (`forget Δ x`,
`bindEnv Γ x (uses body)`) and an arm's body at the arm's binders. -/
inductive Typed : Occs → Occs → Expr → Prop where
  /-- A variable is typed where an environment supplies it, owned or borrowed. -/
  | var {Δ Γ : Occs} {x : Var} (h : x ∈ Γ ∨ x ∈ Δ) : Typed Δ Γ (.var x)
  /-- An abstraction is typed when its body is, its name bound by the binder: the body
  is handed one owned occurrence of the binder's name beside the occurrences its other
  names claim. -/
  | lam {Δ Γ : Occs} {x : Var} {body : Expr}
      (h : Typed (forget Δ x) (bindEnv Γ x (uses body)) body) : Typed Δ Γ (.lam x body)
  /-- An application is typed when both positions are, the environment split between
  the occurrences the term's usage claims for them. -/
  | app {Δ Γ : Occs} {f a : Expr} (hf : Typed Δ (claimEnv Γ (uses f)) f)
      (ha : Typed Δ (claimEnv Γ (uses a)) a) : Typed Δ Γ (.app f a)
  /-- A binding is typed when its two terms are, the second handed one owned occurrence
  of the binder's name beside the occurrences its other names claim. -/
  | bind {Δ Γ : Occs} {x : Var} {e₁ e₂ : Expr} (h₁ : Typed Δ (claimEnv Γ (uses e₁)) e₁)
      (h₂ : Typed (forget Δ x) (bindEnv Γ x (uses e₂)) e₂) : Typed Δ Γ (.bind x e₁ e₂)
  /-- A match is typed when its subject and its arm's body are, the arm handed one owned
  occurrence per binder beside the occurrences the body's other names claim. -/
  | matchC {Δ Γ : Occs} {s : Expr} {c : Ctor} {ys : List Var} {body : Expr}
      (hs : Typed Δ (claimEnv Γ (uses s)) s)
      (h : Typed (forgetAll Δ ys) (armEnv Γ ys (uses body)) body) :
      Typed Δ Γ (.matchC s c ys body)
  /-- A nullary node is typed. -/
  | con0 {Δ Γ : Occs} {c : Ctor} : Typed Δ Γ (.con0 c)
  /-- A unary node is typed when its field is. -/
  | con1 {Δ Γ : Occs} {c : Ctor} {a : Expr} (h : Typed Δ (claimEnv Γ (uses a)) a) :
      Typed Δ Γ (.con1 c a)
  /-- A binary node is typed when its two fields are. -/
  | con2 {Δ Γ : Occs} {c : Ctor} {a b : Expr} (h₁ : Typed Δ (claimEnv Γ (uses a)) a)
      (h₂ : Typed Δ (claimEnv Γ (uses b)) b) : Typed Δ Γ (.con2 c a b)
  /-- The write, with the discipline's own requirement: the subject's variable is owned
  exactly once in the environment of the store and is not borrowed, and the written value
  is typed under the occurrences it claims. -/
  | store {Δ Γ : Occs} {y : Var} {i : Nat} {v : Expr} (hown : Γ.count y = 1)
      (hborrow : y ∉ Δ) (hv : Typed Δ (claimEnv Γ (uses v)) v) :
      Typed Δ Γ (.store (.var y) i v)

/-! ## Every write's subject is owned once and not borrowed

The write's clause is a statement about the environment of the store, and a traversal
of the term carries it: `WriteOwned Δ Γ e` is the same recursion as the typing, asking
at every store that its subject be owned once and not borrowed there. -/

/-- Every write in `e` has, at the environment the typing assigns its position, a
subject owned exactly once there and not borrowed. The recursion is the typing's own,
split by the same functions; a store whose subject is no variable is not disciplined,
which is the shape a typed write never has. -/
def WriteOwned (Δ Γ : Occs) : Expr → Prop
  | .var _ => True
  | .lam x body => WriteOwned (forget Δ x) (bindEnv Γ x (uses body)) body
  | .app f a =>
      WriteOwned Δ (claimEnv Γ (uses f)) f ∧ WriteOwned Δ (claimEnv Γ (uses a)) a
  | .bind x e₁ e₂ =>
      WriteOwned Δ (claimEnv Γ (uses e₁)) e₁
        ∧ WriteOwned (forget Δ x) (bindEnv Γ x (uses e₂)) e₂
  | .matchC s _ ys body =>
      WriteOwned Δ (claimEnv Γ (uses s)) s
        ∧ WriteOwned (forgetAll Δ ys) (armEnv Γ ys (uses body)) body
  | .dup _ _ => True
  | .drop _ _ => True
  | .con0 _ => True
  | .con1 _ a => WriteOwned Δ (claimEnv Γ (uses a)) a
  | .con2 _ a b =>
      WriteOwned Δ (claimEnv Γ (uses a)) a ∧ WriteOwned Δ (claimEnv Γ (uses b)) b
  | .store (.var y) _ v => Γ.count y = 1 ∧ y ∉ Δ ∧ WriteOwned Δ (claimEnv Γ (uses v)) v
  | .store _ _ _ => False

/-- A typed term has every write's subject owned exactly once at its position and not
borrowed: the typing's own write clause, carried by the traversal `WriteOwned`. -/
theorem typed_write_owned {Δ Γ : Occs} {e : Expr} (h : Typed Δ Γ e) :
    WriteOwned Δ Γ e := by
  induction h with
  | var h => trivial
  | lam h ih => exact ih
  | app hf ha ihf iha => exact ⟨ihf, iha⟩
  | bind h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | matchC hs h ihs ih => exact ⟨ihs, ih⟩
  | con0 => trivial
  | con1 h ih => exact ih
  | con2 h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | store hown hborrow hv ihv => exact ⟨hown, hborrow, ihv⟩

/-- A write at the root of a typed term satisfies the write's own requirement: the
subject's variable is owned exactly once in the environment and not borrowed. -/
theorem typed_store_owned {Δ Γ : Occs} {y : Var} {i : Nat} {v : Expr}
    (h : Typed Δ Γ (.store (.var y) i v)) : Γ.count y = 1 ∧ y ∉ Δ := by
  cases h with
  | store hown hborrow _ => exact ⟨hown, hborrow⟩

/-! ## The typing is the lowering's discipline

A typed term is a term of the canonical strategy, from the same environments: the
typing is `Lower`'s environment discipline, restricted to writes whose subject is owned
once, and not a second notion beside it. -/

/-- A name owned exactly once is one an environment holds: its count being one is its
single occurrence. -/
theorem mem_of_count_one {Γ : Occs} {y : Var} (h : Γ.count y = 1) : y ∈ Γ :=
  List.count_pos_iff.mp (by omega)

/-- A name owned exactly once in the environment is claimed by the usage that names it
once: the occurrence the singleton usage asks for is one the environment holds. -/
theorem mem_claimEnv_singleton {Γ : Occs} {y : Var} (h : Γ.count y = 1) :
    y ∈ claimEnv Γ [y] := by
  rw [claimEnv, List.mem_filter]
  exact ⟨by simp, by simpa using mem_of_count_one h⟩

/-- A typed term is lowered by the canonical strategy from the same environments: the
typing's splits are the lowering's, so the typing's derivation is a lowering's. -/
theorem typed_lowers {Δ Γ : Occs} {e : Expr} (h : Typed Δ Γ e) : ∃ e', Lower Δ Γ e e' := by
  induction h with
  | var h => exact ⟨_, Lower.var h⟩
  | lam h ih =>
      obtain ⟨body', hb⟩ := ih
      exact ⟨_, Lower.lam hb⟩
  | app hf ha ihf iha =>
      obtain ⟨f', hf'⟩ := ihf
      obtain ⟨a', ha'⟩ := iha
      exact ⟨_, Lower.app hf' ha'⟩
  | bind h₁ h₂ ih₁ ih₂ =>
      obtain ⟨e₁', h₁'⟩ := ih₁
      obtain ⟨e₂', h₂'⟩ := ih₂
      exact ⟨_, Lower.bind h₁' h₂'⟩
  | matchC hs h ihs ih =>
      obtain ⟨s', hs'⟩ := ihs
      obtain ⟨body', hb⟩ := ih
      exact ⟨_, Lower.matchC hs' hb⟩
  | con0 => exact ⟨_, Lower.con0⟩
  | con1 h ih =>
      obtain ⟨a', ha⟩ := ih
      exact ⟨_, Lower.con1 ha⟩
  | con2 h₁ h₂ ih₁ ih₂ =>
      obtain ⟨a', ha⟩ := ih₁
      obtain ⟨b', hb⟩ := ih₂
      exact ⟨_, Lower.con2 ha hb⟩
  | store hown hborrow hv ihv =>
      obtain ⟨v', hv'⟩ := ihv
      exact ⟨_, Lower.store (Lower.var (Or.inl (mem_claimEnv_singleton hown))) hv'⟩

/-! ## A program that writes to a name and also uses it has no typing

The write's clause is a statement about the term, not only about the label the
environment gives it: a program that writes to a name and also uses that name fails
it, and one that writes to a name it uses once meets it. The chosen programs are
closed, so their typing is read at the empty environments. -/

/-- The program that binds `0`, writes slot `0` of the cell `0` names, and also uses
`0` as the written value: the write's subject is used twice. -/
def dupValue : Expr := .lam 0 (.con1 7 (.store (.var 0) 0 (.var 0)))

/-- The program with the extra use replaced by a fresh closed value: it writes to a
name it uses once. -/
def ownedValue : Expr := .lam 0 (.con1 7 (.store (.var 0) 0 (.con0 9)))

/-- The program whose arm binds the cell's name twice, then writes to it: the subject is
supplied twice by the binder list. -/
def dupArm : Expr := .matchC (.con1 5 (.con0 5)) 0 [0, 0] (.store (.var 0) 0 (.con0 9))

/-- The same program whose arm binds the name once: the write's subject is used once. -/
def ownedArm : Expr := .matchC (.con1 5 (.con0 5)) 0 [0] (.store (.var 0) 0 (.con0 9))

/-- The program whose write's subject is also the written value has no typing: the
store's environment carries two occurrences of `0`, and the write's clause asks for one.
`ScidoniaTest/Typing` reads the same statement and its disciplined control. -/
theorem dupValue_no_typing : ¬ Typed [] [] dupValue := by
  intro h
  unfold dupValue at h
  cases h with
  | lam h => cases h with
    | con1 h => cases h with
      | store hown => exact absurd hown (by decide)

/-- A program whose arm binds the write's subject twice has no typing: the arm's binder
list supplies the name twice, and the write's clause asks for one occurrence. This is
the duplication at the binder list rather than at the written value. -/
theorem dupArm_no_typing : ¬ Typed [] [] dupArm := by
  intro h
  unfold dupArm at h
  cases h with
  | matchC _ h => cases h with
    | store hown => exact absurd hown (by decide)

/-- The disciplined program is typed: the write's subject is used once, as the
subject. -/
theorem ownedValue_typed : Typed [] [] ownedValue := by
  unfold ownedValue
  refine Typed.lam (x := 0) ?_
  refine Typed.con1 ?_
  refine Typed.store (by decide) (by decide) ?_
  exact Typed.con0

/-- The disciplined arm program is typed: the arm binds the write's subject once. -/
theorem ownedArm_typed : Typed [] [] ownedArm := by
  unfold ownedArm
  refine Typed.matchC ?_ ?_
  · refine Typed.con1 ?_
    exact Typed.con0
  · refine Typed.store (by decide) (by decide) ?_
    exact Typed.con0

/-- The sibling of a write does not inflate its environment: a store's environment is
the occurrences its own usage claims, so a name used in a sibling is not counted at the
store. The program below writes to `0` and uses `0` in a sibling position, and is typed
--- the extra use is supplied by a `dup` the lowering emits, not by the store's account.
This is the control that shows the refutations above are about the *store's* own
occurrences and not about a name used anywhere. -/
theorem sibling_use_typed : Typed [] [] (.lam 0 (.con1 7
    (.con2 8 (.store (.var 0) 0 (.con0 9)) (.var 0)))) := by
  refine Typed.lam (x := 0) ?_
  refine Typed.con1 ?_
  refine Typed.con2 ?_ ?_
  · refine Typed.store (by decide) (by decide) ?_
    exact Typed.con0
  · exact Typed.var (Or.inl (by decide))

/-- A `dup` node has no typing: the source fragment has no rule for a resource
instruction, and a typed write's subject could not be supplied twice anyway. -/
theorem dup_no_typing {Δ Γ : Occs} {y : Var} {e : Expr} : ¬ Typed Δ Γ (.dup y e) := by
  intro h
  cases h

/-- A `drop` node has no typing: the source fragment has no rule for a resource
instruction. -/
theorem drop_no_typing {Δ Γ : Occs} {y : Var} {e : Expr} : ¬ Typed Δ Γ (.drop y e) := by
  intro h
  cases h

/-! ## The typing and the source's reduction

The typing is stated over the source fragment, and the reduction stays in it: a typed
term is pure, and every term a run of it reaches is pure. This is the half of "the
typing survives the source's reduction" that the judgement's own clauses give
directly, and it is what makes the typing a statement about λPure rather than about
the whole syntax.

The other half --- that a typed term's *environments* survive a step --- is not a
theorem at the environments the step starts from, and the value restriction a
substitution semantics needs is not a shape condition on the term: consider
`typed` at `Δ = []`, `Γ = [5, 5]` of the redex `(λ0. store (var 0) 0 (var 5)) (var 5)`.
Its write's clause is met at body environment `[0, 5, 5]` (the subject's occurrence is
the binder's single `0`), and the argument's at `[5, 5]`. The contractum
`store (var 5) 0 (var 5)` is typed at `[]`, `[5]` --- the write's clause asks for the
subject's occurrence to be single --- but not at `[]`, `[5, 5]`, because substituting
the *variable* `5` for the binder puts its occurrences where the binder's one
occurrence was, and the environment's two occurrences of `5` then fail the write's
clause. The step consumes an occurrence the redex's own environments do not record, so
survival needs the substituted term to be a *variable* that is linear in the
environment and not borrowed (`Γ.count y = 1`, `y ∉ Δ`), not merely a value. Stating
that lemma needs the environment theory a *filter-multiset* comparison of the two
derivations gives (the environment at a position is a `filter` of the environment at
its parent, so the two derivations' environments agree exactly where the term's
usages agree); that theory is not built here, and the counterexample above is why the
same-environment statement cannot be used in its place. -/

/-- A typed term is a term of the source fragment: the typing has no rule for a `dup`
or a `drop`, so a typed term mentions neither. -/
theorem typed_pure {Δ Γ : Occs} {e : Expr} (h : Typed Δ Γ e) : Pure e := by
  induction h with
  | var h => exact Pure.var _
  | lam h ih => exact Pure.lam ih
  | app hf ha ihf iha => exact Pure.app ihf iha
  | bind h₁ h₂ ih₁ ih₂ => exact Pure.bind ih₁ ih₂
  | matchC hs h ihs ih => exact Pure.matchC ihs ih
  | con0 => exact Pure.con0 _
  | con1 h ih => exact Pure.con1 ih
  | con2 h₁ h₂ ih₁ ih₂ => exact Pure.con2 ih₁ ih₂
  | store hown hborrow hv ihv => exact Pure.store (Pure.var _) ihv

/-- A step of the source's reduction keeps the term it reaches in the fragment a typed
term lies in: the typing survives the reduction as the fragment's own closure. -/
theorem typed_step_pure {Δ Γ : Occs} {e e' : Expr} (h : Typed Δ Γ e) (hs : Step e e') :
    Pure e' :=
  step_preserves_pure hs (typed_pure h)

/-- Along any run of the source's reduction, a term reached from a typed term is still
in the fragment the typing is stated over. -/
theorem typed_run_pure {Δ Γ : Occs} {e e' : Expr} (h : Typed Δ Γ e)
    (hs : StepStar e e') : Pure e' :=
  pure_steps_pure hs (typed_pure h)

/-- A typed write is not the source's slot update: the write's subject is a variable,
and the slot update has no case for a variable, so a typed write has no such redex. The
write's effect is expressed at the target's store and not by the source's own write
rule. -/
theorem typed_store_no_root_update {Δ Γ : Occs} {y : Var} {i : Nat} {v : Expr}
    (_h : Typed Δ Γ (.store (.var y) i v)) :
    ¬ ∃ n', Root (.store (.var y) i v) n' := by
  rintro ⟨n', hr⟩
  cases hr with
  | storeVal _ _ hup => exact absurd hup (by simp [slotUpdate])

end Scidonia.RC
