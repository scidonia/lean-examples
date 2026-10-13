/-
The discipline the target's write needs: what it is for a term to be *run at an
account*, the clause a write's subject has to satisfy under it, and the condition
on the environment under which the account's count at the subject's cell is one.

`Scidonia.RC.Ownership` states what the target's write does at a subject the term
owns once and what it does otherwise, but its two premises --- the term's own
occurrence of the subject (`Owns`) and the account counting that occurrence once
--- are premises nothing in the development supplies. This module supplies them, as
a *judgement* of the term against the account rather than as an identity between
the account and a computation on the term's free variables.

**Why a judgement, and not an identity.** The reading this module replaces fixes
the account as the term's free occurrences read through the environment: `uses`
gives the term's free occurrences, `refsOf` reads a list of names at the references
the environment binds them to, and the account is required to *be* that list. The
runtime's own rules refute it. A `dup y; e` *supplies* an occurrence: the rule
leaves the account one occurrence above the body's own, because `uses` had already
counted the instruction's own name besides the body's occurrences, and
`dup_step_overtakes_own` below is that refutation, kept here as the reason for the
change. A rule that *consumes a value* leaves the value's own occurrences in the
account while the result's free occurrences have none of them, so the account the
rule leaves is wider than the result's own. And a binding moves the value's
occurrence onto the binder, which an identity preserves only when the binder occurs
exactly once in the body --- a linearity the identity does not supply and the rules
do not ask for. An identity with a free-variable computation cannot survive the
rules; a judgement whose every clause *is* the rule's premise and movement survives
them at its instructions, which is what the theorems below state.

**The judgement.** `Runs ρ m e` reads "the term `e` is run at the account `m`", with
one clause per construct, each clause the premise of the target rule that construct
takes together with the account movement that rule makes, read root-first:

* a variable's clause is that the environment binds it and the account holds the
  pair of its name and that reference;
* an abstraction's, a nullary node's, a unary node's and a binary node's clauses are
  the value's own occurrences: a closure holds none and its body's free variables are
  read from the environment when it is applied, a node's fields run, and a binary
  node's first field is a value --- the order the realization of its fields reads
  them in;
* a `dup`'s clause is that the environment binds its name and the *continuation*
  runs at the account with one more occurrence;
* a `drop`'s clause is that the environment binds its name, the account holds the
  occurrence, and the continuation runs at the account with that occurrence removed;
* a binding's clause is that the occurrence its bound variable names moves as the
  rule moves it --- onto the binder, off the value's variable --- and the body runs
  at the environment and account the rule leaves; at an allocated value the binder
  takes the reference over and the body runs at the account with the binder's
  occurrence added;
* an application's clauses are the same moves at the abstraction's parameter;
* a match's clause is that the environment binds its subject's name, the account
  holds that occurrence, and the arm's body runs at the same account once the arm's
  binders name references the account pairs with them;
* a store's clause carries the discipline's own requirement: the account holds the
  store's occurrence (`Owns`), the environment's reference for the subject's name is
  counted once in the account, and the value and the rest of the term run;
* a term whose position holds a computation runs when that position runs and the
  rest of the term is what the position's clause asks for.

The clauses of a construct are exclusive by the shape they name --- a function
position is an abstraction, another value or a computation, and each shape has its
own clause --- so a derivation says which rule it is about, which is what makes the
preservation proofs below case analyses on the derivation's clause.

**The distinctness is an explicit conjunct.** The store's clause carries
`(expand m).count r = 1` for the reference the environment names for its subject,
rather than deriving that count from a condition on the term's free variables. That
is the distinctness `Ownership.store_owned_is_destructive` needs beside the
occurrence --- its `hm` beside its `hown` --- and making it a conjunct of the
judgement is what lets `runs_store_owned` read the two hypotheses off a derivation
directly.

**What is preserved.** Every instruction of the relation preserves the judgement, each
by its own clause: `runs_dup`, `runs_drop` (the release's two branches are one move of
the account, since the cell's count decides the heap's move and not the account's),
`runs_bindVar`, `runs_bindVal`, `runs_appVar`, `runs_appVal`, `runs_storeExclusive` and
`runs_storeShared` (the write's two branches likewise). Of the congruence rules --- the
steps that reach a term's positions --- three preserve it once the position's own
preservation is at hand, and they are stated with that preservation as a hypothesis,
because that is exactly what the induction over the relation gives a congruence rule
about its position's step: `runs_con1Field`, `runs_con2FieldL` (whose case is vacuous:
the clause asks a binary node's first field to be a value, and `value_does_not_step`)
and `runs_con2FieldR`.

**Where the target's rules do not preserve it.** Four rules do not, and they are a
finding about the relation's own shape rather than about a missing clause: the
judgement's positional clauses read a term's positions at the *whole*
configuration's account and environment, and these rules step a position there while
leaving its sibling in place.

* `appFun` and the first family of `appArg`: a clause reads the sibling position's
  own judgement at the configuration the step starts from, and the step may move the
  environment or consume an occurrence the sibling's clause rests on. The judgement
  admits the state where two positions' requirements rest on one occurrence --- its
  clauses are the rules' premises, and the rules' premises are membership in the
  configuration's account --- and a step in one position then removes the ground
  under the other's clause.
* the second family of `appArg`, and `bindRhs`: a position whose step produces a
  *value* meets the clause for a term whose position is that value, and that clause
  carries the continuation the rule runs --- the body's own judgement at the moved
  environment and account. A clause for a position that holds a computation carries
  the position's judgement and not that continuation, so the value-shaped conclusion
  asks for something the computation-shaped configuration never supplied.
* `matchC`: the rule binds the arm's binders to the *cell's slots*, which are the
  heap's, and leaves the account unchanged; a heap-free judgement can only ask the
  body to run at bindings the account pairs with the binders, and the rule's own
  premise that the binders shadow none of the account's names makes that demand
  vacuous on the configurations the rule fires at, so the body's own clause is not
  re-established at the arm it leaves.

The exact goals and the counterexamples are `ScidoniaTest/Discipline`'s
`appFun_account_shared`, `appArg_value_not_reached`, `bindRhs_value_not_reached` and
`matchC_arm_not_paired`. Each failing goal is stated with the account and
environment the step starts from and leaves; none of them is a clause the judgement
is missing, and none is hidden by restricting the judgement.

**What is modelled, and what is trusted.** The judgement is a static reading of a
configuration: the environment, the term's own multiplicities and the term, with no
reference to the heap, so its clauses are the rules' *logical* premises and not the
heap's own operations. A derivation is evidence of the discipline, not of the rules
having fired: the judgement says what a term run at an account needs, and the
theorems say what each rule's move costs it. A closure is judged holding no
occurrence --- the model's closures capture nothing --- so its body is judged where
an application or a binding resumes it, and an abstraction never applied is judged
without its body. The account is read as a multiset in list form, and the write's
branch is `RCHeap.update`'s, as `Ownership` states it. Nothing here is about
compiled code.
-/
import Scidonia.RC.Ownership

namespace Scidonia.RC

open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap

/-! ## Reading a list of names through an environment

A list of names is read two ways: at the references the environment binds them to
(`refsOf`), and at the pairs of a name and its reference (`pairsOf`). A name the
environment binds nowhere contributes to neither. The readings are what the checks
compare an account against; the judgement below does not compute the account out of
the term, and `dup_step_overtakes_own` is the reason. -/

/-- The references a list of names is read at, in order. -/
def refsOf (rho : TEnv) (us : List Var) : List Ref := us.filterMap (fun x => rho.lookup x)

/-- The pairs a list of names names, in order: one pair per name, the name and the
reference the environment binds it to. -/
def pairsOf (rho : TEnv) (us : List Var) : Multi :=
  us.filterMap (fun x => (rho.lookup x).map (fun r => (x, r)))

/-- The pairs the term's free occurrences name: the term's own occurrences, one pair
per occurrence, each occurrence's variable and the reference the environment binds
it to. -/
def occsOf (rho : TEnv) (e : Expr) : Multi := pairsOf rho (uses e)

/-- A term's own occurrences are its free occurrences read at the pairs: the two
spellings are the same list. -/
theorem occsOf_pairsOf (rho : TEnv) (e : Expr) : occsOf rho e = pairsOf rho (uses e) := rfl

/-- An empty list names nothing. -/
@[simp] theorem refsOf_nil (rho : TEnv) : refsOf rho [] = [] := rfl

/-- An empty list names no pair. -/
@[simp] theorem pairsOf_nil (rho : TEnv) : pairsOf rho [] = ([] : Multi) := rfl

/-- A list of names the environment binds contributes its first pair. -/
@[simp] theorem pairsOf_cons_some {rho : TEnv} {x : Var} {r : Ref}
    (h : rho.lookup x = some r) (us : List Var) :
    pairsOf rho (x :: us) = (x, r) :: pairsOf rho us := by
  simp [pairsOf, h]

/-- A name the environment binds nowhere contributes no pair. -/
@[simp] theorem pairsOf_cons_none {rho : TEnv} {x : Var} (h : rho.lookup x = none)
    (us : List Var) : pairsOf rho (x :: us) = pairsOf rho us := by
  simp [pairsOf, h]

/-- The pairs a `dup` node's free occurrences name: the occurrence the instruction
supplies and its body's. -/
theorem occsOf_dup {rho : TEnv} {y : Var} {r : Ref} {e : Expr} (h : rho.lookup y = some r) :
    occsOf rho (.dup y e) = (y, r) :: occsOf rho e := by
  change pairsOf rho (y :: uses e) = (y, r) :: pairsOf rho (uses e)
  rw [pairsOf_cons_some h]

/-- The occurrence a `drop` supplies is the first the list it leaves holds, so the
account a release leaves is the one it was handed back. -/
@[simp] theorem dropOcc_insert_self (m : Multi) (y : Var) (r : Ref) :
    Multi.dropOcc (Multi.insert m y r) y r = m := by
  simp [Multi.insert, Multi.dropOcc]

/-- The pair a `dup` supplies is counted once more than the list it joins counts it. -/
@[simp] theorem count_insert_self (m : Multi) (y : Var) (r : Ref) :
    (Multi.insert m y r).count (y, r) = m.count (y, r) + 1 := by
  simp [Multi.insert]

/-- The reading this module replaces is refuted by the `dup` rule: the account the
rule leaves holds one occurrence more than the body's own free occurrences, and the
body's own account is the body of the rule's account --- the instruction's own
occurrence is still on it, because `uses` counts the instruction's name besides its
body's occurrences. An account that *is* the term's free occurrences read through the
environment therefore cannot survive the instruction: the rule's step leaves
`insert (occsOf ρ (.dup y e)) y r`, and that list is not `occsOf ρ e`. -/
theorem dup_step_overtakes_own {rho : TEnv} {e : Expr} {y : Var} {r : Ref}
    (h : rho.lookup y = some r) :
    Multi.dropOcc (Multi.insert (occsOf rho (.dup y e)) y r) y r = occsOf rho (.dup y e)
      ∧ Multi.insert (occsOf rho (.dup y e)) y r ≠ occsOf rho e := by
  refine ⟨dropOcc_insert_self _ _ _, ?_⟩
  intro heq
  have hcount : (Multi.insert (occsOf rho (.dup y e)) y r).count (y, r)
      = (occsOf rho e).count (y, r) + 2 := by
    rw [count_insert_self, occsOf_dup h]
    simp
  rw [heq] at hcount
  omega

/-! ## The discipline: a term run at an account

`Runs` is the judgement this module is for. Each clause is one construct of
`Scidonia.RC.Syntax`'s syntax, and each is the premise of the target rule that
construct takes, together with the account movement that rule makes, read
root-first: the outer instruction's premise and movement, and the continuation's own
clause. -/

/-- The term `e` is run at the account `m` in the environment `ρ`: the judgement the
target's rules preserve at their instructions. The environment is an index of the
judgement and not a parameter, because a clause's continuation runs at the
environment the rule leaves --- a binding's body at the binding's own environment,
an arm's body at the arm's binders --- and a uniform parameter could not hold it. -/
inductive Runs : TEnv → Multi → Expr → Prop where
  /-- A variable is a value whose occurrence the account holds, at the reference the
  environment names for it. -/
  | var {ρ : TEnv} {x : Var} {r : Ref} {m : Multi} (hρ : ρ.lookup x = some r)
      (hmem : (x, r) ∈ m) : Runs ρ m (.var x)
  /-- An abstraction is a value that holds no occurrence: the closure captures
  nothing, and its body's free variables are read from the environment in force when
  it is applied. -/
  | lam {ρ : TEnv} (x : Var) (body : Expr) (m : Multi) : Runs ρ m (.lam x body)
  /-- A nullary node is a value that holds no occurrence. -/
  | con0 {ρ : TEnv} (c : Ctor) (m : Multi) : Runs ρ m (.con0 c)
  /-- A unary node's field runs: its cell is allocated with the field's reference as
  its only slot. -/
  | con1 {ρ : TEnv} {c : Ctor} {a : Expr} {m : Multi} (h : Runs ρ m a) :
      Runs ρ m (.con1 c a)
  /-- A binary node's first field is a value and its second field runs: the
  realization reads the fields in that order. -/
  | con2 {ρ : TEnv} {c : Ctor} {a b : Expr} {m : Multi} (ha : Value a) (hb : Runs ρ m b) :
      Runs ρ m (.con2 c a b)
  /-- A `dup` supplies an occurrence: the environment binds its name and the
  continuation runs at the account with one more occurrence. -/
  | dup {ρ : TEnv} {y : Var} {r : Ref} {e : Expr} {m : Multi} (hρ : ρ.lookup y = some r)
      (h : Runs ρ (Multi.insert m y r) e) : Runs ρ m (.dup y e)
  /-- A `drop` releases an occurrence the account holds: the continuation runs at the
  account with it removed. -/
  | drop {ρ : TEnv} {y : Var} {r : Ref} {e : Expr} {m : Multi} (hρ : ρ.lookup y = some r)
      (hmem : (y, r) ∈ m) (h : Runs ρ (Multi.dropOcc m y r) e) : Runs ρ m (.drop y e)
  /-- A binding of a variable moves the value's occurrence onto the binder, and the
  body runs at the environment and account the rule leaves. The binder's name holds
  no occurrence of the account at another reference, because it reads the value's
  reference from then on. -/
  | bindVar {ρ : TEnv} {x z : Var} {r : Ref} {e₂ : Expr} {m : Multi}
      (hρ : ρ.lookup z = some r) (hmem : (z, r) ∈ m) (hhigh : nameOnly m x r = true)
      (h : Runs (TEnv.set ρ x r) (Multi.insert (Multi.dropOcc m z r) x r) e₂) :
      Runs ρ m (.bind x (.var z) e₂)
  /-- A binding of an allocated value: the binder takes the reference the realization
  handed out, and the body runs at the account with the binder's occurrence added.
  The bound term is no variable, and the binder's name holds no occurrence of the
  account. -/
  | bindVal {ρ : TEnv} {x : Var} {v e₂ : Expr} {m : Multi} (hnovar : ∀ z, v ≠ .var z)
      (hval : Value v) (hfree : freeName m x = true)
      (h : ∀ r, Runs (TEnv.set ρ x r) (Multi.insert m x r) e₂) :
      Runs ρ m (.bind x v e₂)
  /-- A binding whose bound term is a computation: the position runs and the body
  runs. -/
  | bindPos {ρ : TEnv} {x : Var} {e₁ e₂ : Expr} {m : Multi} (hval : ¬ Value e₁)
      (h₁ : Runs ρ m e₁) (h₂ : Runs ρ m e₂) : Runs ρ m (.bind x e₁ e₂)
  /-- An application of an abstraction to a variable moves the argument's occurrence
  onto the parameter, and the body runs at the environment and account the rule
  leaves. -/
  | appVar {ρ : TEnv} {x z : Var} {r : Ref} {body : Expr} {m : Multi}
      (hρ : ρ.lookup z = some r) (hmem : (z, r) ∈ m) (hhigh : nameOnly m x r = true)
      (h : Runs (TEnv.set ρ x r) (Multi.insert (Multi.dropOcc m z r) x r) body) :
      Runs ρ m (.app (.lam x body) (.var z))
  /-- An application of an abstraction to an allocated value resumes the body at the
  reference the realization handed out. -/
  | appVal {ρ : TEnv} {x : Var} {v body : Expr} {m : Multi} (hnovar : ∀ z, v ≠ .var z)
      (hval : Value v) (hfree : freeName m x = true)
      (h : ∀ r, Runs (TEnv.set ρ x r) (Multi.insert m x r) body) :
      Runs ρ m (.app (.lam x body) v)
  /-- An application whose function is a computation: the function position runs and
  the argument runs. -/
  | appPos {ρ : TEnv} {f a : Expr} {m : Multi} (hval : ¬ Value f) (hf : Runs ρ m f)
      (ha : Runs ρ m a) : Runs ρ m (.app f a)
  /-- An application whose function is a value that is not an abstraction: the
  argument runs. The function is not read for an occurrence, which is what the
  argument's rule asks of it. -/
  | appArgPos {ρ : TEnv} {f a : Expr} {m : Multi} (hval : Value f)
      (hnotlam : ∀ x body, f ≠ .lam x body) (ha : Runs ρ m a) : Runs ρ m (.app f a)
  /-- An application of an abstraction to a computation: the argument runs. -/
  | appLamArg {ρ : TEnv} {x : Var} {body a : Expr} {m : Multi} (hval : ¬ Value a)
      (ha : Runs ρ m a) : Runs ρ m (.app (.lam x body) a)
  /-- A match binds the arm's binders to the slots of the cell its subject names, and
  leaves the account as it was. The body runs once the binders name references the
  account pairs with them; the arm's binders receive the cell's slots, which are the
  heap's, so the pairs are the hypothesis the clause carries. -/
  | matchC {ρ : TEnv} {z : Var} {r : Ref} {c : Ctor} {ys : List Var} {body : Expr}
      {m : Multi} (hρ : ρ.lookup z = some r) (hmem : (z, r) ∈ m)
      (h : ∀ rs, ys.length = rs.length → (∀ p ∈ ys.zip rs, p ∈ m) →
        Runs (TEnv.bindAll ρ ys rs) m body) : Runs ρ m (.matchC (.var z) c ys body)
  /-- A store, with the discipline's own requirement: the account holds the store's
  occurrence (`Owns`), the reference the environment names for its subject is counted
  once in the account, and the value and the rest of the term run. -/
  | store {ρ : TEnv} {y : Var} {i : Nat} {v : Expr} {m : Multi}
      (hown : Owns ρ m (.store (.var y) i v))
      (hdistinct : ∀ r, ρ.lookup y = some r → (expand m).count r = 1)
      (hv : Runs ρ m v) (hy : Runs ρ m (.var y)) : Runs ρ m (.store (.var y) i v)

/-! ## Values do not step, and a realized value is a value

The clause of a binary node asks its first field to be a value, which is what makes
the first field's congruence rule vacuous: no rule of the relation starts from a
value. The lemma is by induction on the value, each case closed by the shape of the
rules' conclusions. -/

/-- A value takes no step of the target relation: every rule of `Scidonia.RC.Target`
starts from an instruction, and no instruction is a value. -/
theorem value_does_not_step {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {e : Expr}
    {c' : CHeap} {hs' : List Ref} {ρ' : TEnv} {m' : Multi} (hv : Value e) :
    ∀ {e' : Expr}, ¬ TStep c hs ρ m e c' hs' ρ' m' e' := by
  induction hv with
  | var x => intro e' h; cases h
  | lam x body => intro e' h; cases h
  | con0 c => intro e' h; cases h
  | con1 ha ih =>
      intro e' h
      cases h with
      | con1Field hstep => exact ih hstep
  | con2 ha hb iha ihb =>
      intro e' h
      cases h with
      | con2FieldL hstep => exact iha hstep
      | con2FieldR _ hstep => exact ihb hstep

/-- A realized value is a value: the realization's clauses are the value forms one by
one. -/
theorem valRef_value : ∀ {c : CHeap} {hs : List Ref} {ρ : TEnv} {v : Expr} {c' : CHeap}
    {hs' : List Ref} {r : Ref}, ValRef c hs ρ v c' hs' r → Value v
  | _, _, _, _, _, _, _, ValRef.var _ _ => Value.var _
  | _, _, _, _, _, _, _, ValRef.lam => Value.lam _ _
  | _, _, _, _, _, _, _, ValRef.con0 => Value.con0 _
  | _, _, _, _, _, _, _, ValRef.con1 hv _ => Value.con1 (valRef_value hv)
  | _, _, _, _, _, _, _, ValRef.con2 hv₁ hv₂ _ _ =>
      Value.con2 (valRef_value hv₁) (valRef_value hv₂)

/-! ## The discipline implies the store's hypotheses -/

/-- A term run at an account whose store is disciplined gives the store's two
hypotheses: the account holds the store's occurrence (`Owns`), and the reference the
environment names for the subject is counted once in the account. The second is the
clause's own distinctness conjunct, which is the reading
`Ownership.store_owned_is_destructive` consumes as its `hm`. -/
theorem runs_store_owned {ρ : TEnv} {m : Multi} {y : Var} {i : Nat} {v : Expr}
    (h : Runs ρ m (.store (.var y) i v)) :
    Owns ρ m (.store (.var y) i v) ∧ ∃ r, ρ.lookup y = some r ∧ (expand m).count r = 1 := by
  cases h with
  | store hown hdistinct _ _ =>
      obtain ⟨r, hρ, _⟩ := hown.store_occurrence
      exact ⟨hown, r, hρ, hdistinct r hρ⟩

/-- The store's own occurrence under the judgement: the pair of the subject's
variable and the reference the environment names for it is one the account holds. -/
theorem runs_store_occurrence {ρ : TEnv} {m : Multi} {y : Var} {i : Nat} {v : Expr}
    (h : Runs ρ m (.store (.var y) i v)) : ∃ r, ρ.lookup y = some r ∧ (y, r) ∈ m :=
  (runs_store_owned h).1.store_occurrence

/-! ## The moves the instruction rules make

One theorem per instruction of the step relation, each reading the clause of the
judgement its term is judged by. Each states the rule's move: the rule's own premises
and the judgement at the term the rule fires at give the judgement at the
configuration the rule leaves. Every one of them is the clause itself --- a `dup`'s
continuation is the clause's continuation, a `drop`'s is the clause's, and a binding's
and an application's continuations are the clauses' continuations --- and the shape
alternatives the other clauses are excluded by. A name is read at one reference, so
the reference the rule's premise names and the reference the clause names agree, which
is `lookup_unique`. The theorems are about the rule and not about the whole relation:
a term that a rule fires at may also be a position a congruence rule steps, and the
four goals in the module note are exactly what the congruence rules then ask for.

The store's two branches are one move of the account --- the write's branch is the
heap's count --- so the two theorems below read the same clause and differ in the
configuration the rule leaves. -/

/-- The environment reads a name at one reference: two hypotheses that bind it agree. -/
theorem lookup_unique {ρ : TEnv} {x : Var} {r r' : Ref} (h : ρ.lookup x = some r)
    (h' : ρ.lookup x = some r') : r = r' :=
  Option.some.inj (h.symm.trans h')

/-- A `dup` step preserves the judgement: the rule leaves exactly the continuation the
clause asks for, at the account with the occurrence the instruction supplies. -/
theorem runs_dup {ρ : TEnv} {m : Multi} {y : Var} {r : Ref} {e : Expr}
    (hρ : ρ.lookup y = some r) (h : Runs ρ m (.dup y e)) :
    Runs ρ (Multi.insert m y r) e := by
  cases h with
  | dup hρ' h' =>
      rw [lookup_unique hρ' hρ] at h'
      exact h'

/-- A release preserves the judgement, both of the relation's branches: the cell's
count decides the heap's move and not the account's, so the step leaves the
continuation the clause asks for, at the account with the released occurrence
removed. -/
theorem runs_drop {ρ : TEnv} {m : Multi} {y : Var} {r : Ref} {e : Expr}
    (hρ : ρ.lookup y = some r) (_hsub : (y, r) ∈ m) (h : Runs ρ m (.drop y e)) :
    Runs ρ (Multi.dropOcc m y r) e := by
  cases h with
  | drop hρ' _ h' =>
      rw [lookup_unique hρ' hρ] at h'
      exact h'

/-- A binding of a variable preserves the judgement: the step's environment and
account are the clause's own, so its continuation is the clause's continuation. -/
theorem runs_bindVar {ρ : TEnv} {m : Multi} {x z : Var} {r : Ref} {e₂ : Expr}
    (hρ : ρ.lookup z = some r) (_hsub : (z, r) ∈ m) (_hhigh : nameOnly m x r = true)
    (h : Runs ρ m (.bind x (.var z) e₂)) :
    Runs (TEnv.set ρ x r) (Multi.insert (Multi.dropOcc m z r) x r) e₂ := by
  cases h with
  | bindVar hρ' _ _ h' =>
      rw [lookup_unique hρ' hρ] at h'
      exact h'
  | bindVal hnovar _ _ _ => exact absurd rfl (hnovar z)
  | bindPos hval _ _ => exact absurd (Value.var z) hval

/-- A binding of an allocated value preserves the judgement: the clause asks the body
to run at every binding of the binder, so the step's own reference is one instance of
it. -/
theorem runs_bindVal {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x : Var}
    {v e₂ : Expr} {c' : CHeap} {hs' : List Ref} {r : Ref} (hv : ValRef c hs ρ v c' hs' r)
    (halloc : ∀ z, v ≠ .var z) (_hfree : freeName m x = true)
    (h : Runs ρ m (.bind x v e₂)) : Runs (TEnv.set ρ x r) (Multi.insert m x r) e₂ := by
  cases h with
  | bindVal _ _ _ h' => exact h' r
  | bindVar _ _ _ _ => exact absurd rfl (halloc _)
  | bindPos hval _ _ => exact absurd (valRef_value hv) hval

/-- An application of an abstraction to a variable preserves the judgement: the step's
environment and account are the clause's own, so its continuation is the clause's
continuation. -/
theorem runs_appVar {ρ : TEnv} {m : Multi} {x z : Var} {r : Ref} {body : Expr}
    (hρ : ρ.lookup z = some r) (_hsub : (z, r) ∈ m) (_hhigh : nameOnly m x r = true)
    (h : Runs ρ m (.app (.lam x body) (.var z))) :
    Runs (TEnv.set ρ x r) (Multi.insert (Multi.dropOcc m z r) x r) body := by
  cases h with
  | appVar hρ' _ _ h' =>
      rw [lookup_unique hρ' hρ] at h'
      exact h'
  | appVal hnovar _ _ _ => exact absurd rfl (hnovar z)
  | appPos hval _ _ => exact absurd (Value.lam x body) hval
  | appArgPos _ hnotlam _ => exact absurd rfl (hnotlam x body)
  | appLamArg hval _ => exact absurd (Value.var z) hval

/-- An application of an abstraction to an allocated value preserves the judgement:
the clause asks the body to run at every binding of the parameter, so the step's own
reference is one instance of it. -/
theorem runs_appVal {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x : Var}
    {v body : Expr} {c' : CHeap} {hs' : List Ref} {r : Ref} (hv : ValRef c hs ρ v c' hs' r)
    (halloc : ∀ z, v ≠ .var z) (_hfree : freeName m x = true)
    (h : Runs ρ m (.app (.lam x body) v)) :
    Runs (TEnv.set ρ x r) (Multi.insert m x r) body := by
  cases h with
  | appVal _ _ _ h' => exact h' r
  | appVar _ _ _ _ => exact absurd rfl (halloc _)
  | appPos hval _ _ => exact absurd (Value.lam x body) hval
  | appArgPos _ hnotlam _ => exact absurd rfl (hnotlam x body)
  | appLamArg hval _ => exact absurd (valRef_value hv) hval

/-- The destructive branch of a store preserves the judgement: the account and the
environment are what they were, and the write's result is the subject's occurrence,
which the clause holds as its own conjunct. -/
theorem runs_storeExclusive {ρ : TEnv} {m : Multi} {y : Var} {i : Nat} {v : Expr}
    (h : Runs ρ m (.store (.var y) i v)) : Runs ρ m (.var y) := by
  cases h with
  | store _ _ _ hy => exact hy

/-- The copying branch of a store preserves the judgement: the step leaves the
subject's name naming the fresh location, and the write's result is that name's
occurrence, which the account the rule leaves holds as its first pair. -/
theorem runs_storeShared {ρ : TEnv} {m : Multi} {y : Var} {i : Nat} {v : Expr} {r : Ref}
    {fr : Ref} (_h : Runs ρ m (.store (.var y) i v)) :
    Runs (TEnv.set ρ y fr) (Multi.insert (Multi.dropOcc m y r) y fr) (.var y) :=
  Runs.var (TEnv.lookup_set_self ρ y fr) (List.mem_cons_self ..)

/-! ## The congruence rules that preserve the judgement

A congruence rule steps a term's position; the induction over the relation gives such
a rule the position's own preservation as its hypothesis, and the theorems here are
stated with it, because that is exactly what the rule's case has. -/

/-- A step in the field of a unary node preserves the judgement: the node's clause is
the field's clause and the field's step is the position's own preservation. -/
theorem runs_con1Field {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {ct : Ctor}
    {a : Expr} {c' : CHeap} {hs' : List Ref} {ρ' : TEnv} {m' : Multi} {a' : Expr}
    (_h : TStep c hs ρ m a c' hs' ρ' m' a') (hpos : Runs ρ m a → Runs ρ' m' a')
    (hr : Runs ρ m (.con1 ct a)) : Runs ρ' m' (.con1 ct a') := by
  cases hr with
  | con1 h => exact Runs.con1 (hpos h)

/-- A step in the first field of a binary node preserves the judgement: the node's
clause asks that field to be a value, and a value takes no step, so no such
configuration is judged. -/
theorem runs_con2FieldL {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {ct : Ctor}
    {a b : Expr} {c' : CHeap} {hs' : List Ref} {ρ' : TEnv} {m' : Multi} {a' : Expr}
    (h : TStep c hs ρ m a c' hs' ρ' m' a') (hr : Runs ρ m (.con2 ct a b)) :
    Runs ρ' m' (.con2 ct a' b) := by
  cases hr with
  | con2 ha _ => exact (value_does_not_step ha h).elim

/-- A step in the second field of a binary node preserves the judgement: the first
field's value is what it was, and the second field's step is the position's own
preservation. -/
theorem runs_con2FieldR {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {ct : Ctor}
    {a b : Expr} {c' : CHeap} {hs' : List Ref} {ρ' : TEnv} {m' : Multi} {b' : Expr}
    (ha : Value a) (_h : TStep c hs ρ m b c' hs' ρ' m' b') (hpos : Runs ρ m b → Runs ρ' m' b')
    (hr : Runs ρ m (.con2 ct a b)) : Runs ρ' m' (.con2 ct a b') := by
  cases hr with
  | con2 _ hb => exact Runs.con2 ha (hpos hb)

/-! ## The root of a run

A root is the reference the run's object is named by: no slot of the heap names it and
no handle the run holds names it. Those are the two facts a rooted configuration has by
its shape, and they are the two premises `Ownership.store_owned_is_destructive` names
as the ones the account cannot supply. -/

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

/-- A reference no slot of the heap names is counted zero by the heap's slots: the
shape a heap has at a root it does not name. -/
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
judgement supplies the two premises `Ownership.store_owned_is_destructive` cannot
derive --- the term's own occurrence of the subject and the account's counting it
once --- and the root's shape supplies the two hypotheses that theorem names, no slot
of the heap and no handle the run holding naming the cell (`Rooted`). What is left is
the write rule's own check on the written slots (`hks`, `writeCheck`'s third
conjunct): it is the rule's premise and not the discipline's, and it is named here
rather than assumed silently. -/
theorem rooted_store_destructive {c : CHeap} {hs : List Ref} {rho : TEnv} {m : Multi}
    {y : Var} {r : Ref} {i : Nat} {v : Expr} {ks : List Ref}
    (hc : Couple c hs rho m) (hlook : rho.lookup y = some r)
    (hw : Runs rho m (.store (.var y) i v)) (hroot : Rooted c hs r) (hks : r ∉ ks) :
    (update c (hs ++ expand m) r ks).1.lookup r = some ks := by
  obtain ⟨hown, r', hr', hcount⟩ := runs_store_owned hw
  have hrr : r' = r := Option.some.inj (hr'.symm.trans hlook)
  exact store_owned_is_destructive hc hlook hown (hrr ▸ hcount) (Rooted.slot_count hroot)
    (Rooted.handle_count hroot) hks

end Scidonia.RC
