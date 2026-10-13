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
canonical splits, with one rule per construct of the source and no target term, with
the write's clause strengthened to what a destructive write needs, and with two
conditions on the *name* a write's subject carries.

**The write's clause.** A write's rule is the only place where multiplicity and not
membership is read. It requires the subject's variable to be owned exactly once in
the environment of the store (`Γ.count y = 1`) and not borrowed (`y ∉ Δ`): the write
is expressible only where the cell is the term's own, which is what a destructive
write on a cell of reference count one needs. The unrepresentability results below are
that clause's own inversion: a program whose write's subject is also used has no
derivation at the empty environments a closed program is read at, which is the
repository's form of "unwritable".

**What the store's own environment does not say.** That clause reads the environment
*at the store*, and an environment is a `filter` of its parent's, so a name's
occurrences are claimed separately by each position that uses them: shares overlap,
and a sibling's use of the subject's name is not counted at the store. A term whose
write's subject is also used in a sibling position therefore meets the write's clause
--- the store's own occurrence is the subject's --- while the program as a whole holds
the cell twice, and the lowering supplies the sibling's use with a `dup`, which is
exactly the case where the write stops being in place. Reads the store's environment
alone, the typing cannot see the program's multiplicity, so two further conditions are
needed on the name a subject carries. Both are side conditions of the rules that
*bind* that name, and both are proved, not asserted.

* **A written name is used exactly once in the scope that binds it.** `lam` and
  `bind`, and the arm rule of `matchC` for each of its binders, carry
  `writes x body = true → (uses body).count x = 1`: if the body writes the name the
  rule binds, the body uses that name exactly once. `writes` is the traversal below,
  in the style of `uses`: it is true at a write whose subject is the free variable
  `x`, and a binder of `x` stops it. The condition is what makes the *program* hold
  the cell once rather than the store's share of it, and `typed_write_linear` carries
  it over a typed term. The term the earlier reading admitted as its control ---
  `lam 0 (con1 7 (con2 8 (store (var 0) 0 (con0 9)) (var 0)))`, whose sibling's
  `(var 0)` is a second reference to the cell the write lands at --- therefore has no
  typing (`sibling_use_no_typing`), and `sibling_use_owned`, which writes the cell and
  does not use it elsewhere, is its typed counterpart.
* **A written name comes from a construction rather than another name.** The `bind`
  rule carries `writes x e₂ = true → BuiltB e₁ = true`, and the arm rule of `matchC`
  carries `writes y body = true → BuiltB s = true` for each binder `y`: a binding's
  written name is bound to a *node* of the syntax --- a value the program built --- and
  never to `(.var z)`, which would make the written name a second name for a cell the
  program already holds; an arm's binder is matched out of a *subject* that is such a
  node, and the *field* the subject hands the binder may itself be a name --- the case
  the caveat below leaves outside the guarantees. `typed_write_built` carries the
  condition over a typed term, `alias_bind_no_typing` is its inversion --- a program
  that binds a name to another name and writes through the binding has no typing ---
  and `built_bind_typed` is the same shape with the binding a construction.

**Two conditions at a name, not a second judgement.** `typed_write_linear` and
`typed_write_built` are traversals a typed term carries, and the traversals are
`WriteLinear` and `WriteBuilt` below, in the style of `WriteOwned`. The write's own
clause and the two name conditions are therefore three readings of one judgement and
not a second discipline beside it: the typing is still the lowering's environment
discipline, restricted.

**What the two conditions do not reach.** They are stated of the rules that bind a
name *within* the term, and a written name may be one the term binds nowhere: a
subject that is a free variable of the term is the environment's, and the `store` rule
admits it wherever the environment holds it once and it is not borrowed. An
abstraction's name is bound to the argument an application supplies, and no side
condition of an abstraction or an application can see that argument's shape; a
matching arm's binder names a *field* of the matched cell, and a field that is itself a
name is a second name for that name's cell. Those cases --- together with the write
reached through a nested update, where the cell's count of one and the absence of any
other name for it are facts the take-out provides and `Scidonia.RC.Ownership`'s
`store_owned_is_destructive` *names* among its hypotheses rather than deriving ---
remain outside this module. What is proved here is the name side of the write: where
the term itself binds the name a subject carries, that name is used exactly once in
the scope that binds it and is introduced for, or matched out of, a construction.

**Survival.** The typing is preserved by the source's own substitution under a
restriction the name conditions make natural. `subst_typed_var` substitutes the
variable `y` for `x` in a typed term and reads the result at the renamed environments,
and it needs `y` to be a name other than `x` that the term does not mention and the
environments do not hold, and `x` to be a name the term does not rebind. The
restriction is not a property of the substituted term's shape, and `ScidoniaTest/Typing`
carries the witness the earlier reading left as the gap: the redex
`(λ0. store (var 0) 0 (var 5)) (var 5)` is typed at `[]`, `[5, 5]`, and its contractum
`store (var 5) 0 (var 5)` is typed at `[]`, `[5]` and not at `[]`, `[5, 5]`, because
the term names `5` twice and substituting the *variable* `5` for the binder puts its
occurrences where the binder's one occurrence was. A name used twice in the term --
exactly what the first name condition refuses at a binder the term carries -- is what
the same-environment statement cannot survive, and the freshness the lemma asks for is
what excludes it.

## What is proved

* `typed_write_owned`: every write in a typed term has, at the environment the typing
  assigns its position, a subject owned exactly once there and not borrowed; stated as
  the recursive reading `WriteOwned`, which a traversal of the term carries.
* `typed_write_linear`: every binding rule of a typed term whose body writes the name
  it binds uses that name exactly once in the body it binds; stated as the recursive
  reading `WriteLinear`, which a traversal of the term carries.
* `typed_write_built`: every binding rule of a typed term whose body writes the name it
  binds introduces that name for a construction of the program --- the bound term for a
  binding, the matched subject for an arm; stated as the recursive reading `WriteBuilt`,
  which a traversal of the term carries.
* `dupValue_no_typing` and `dupArm_no_typing`: a program whose write's subject is also
  the written value, and one whose arm binds the subject twice, have no typing at the
  empty environments; `ownedValue_typed` and `ownedArm_typed` are the same shapes with
  the subject used once, typed.
* `sibling_use_no_typing` and `alias_bind_no_typing`: a program whose write's subject
  is used in a sibling position, and one that binds a written name to another name,
  have no typing; `sibling_use_owned` and `built_bind_typed` are their typed
  counterparts, and `typed_lam_written_linear`, `typed_bind_written_linear`,
  `typed_arm_written_linear`, `typed_bind_written_built`, `typed_arm_written_built`,
  `typed_bind_written_own` and `typed_arm_written_own` read the two conditions at a
  rule: the name is used once in the scope that binds it, and it is introduced for, or
  matched out of, a construction --- so a binding's program builds the cell the write
  lands at and names it once, while an arm's program builds the matched subject and the
  binder names a field of it, whose own construction the condition leaves open ---
  source-level facts of construction and use, and not a count on the target heap.
* `typed_lowers`: a typed term is a term `Scidonia.RC.Lower` lowers from the same
  environments.
* `subst_typed_var` and `subst_typed_redex`: a typed term stays typed under the
  substitution of a fresh variable for a name it does not rebind, read at the renamed
  environments --- and at the environments the abstraction rule of a redex leaves.
* `typed_pure` and `typed_run_pure`: a typed term is of the source fragment and stays
  in it along any run --- the half of survival the judgement's own clauses give.

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
occurrence was, and the environment's two then fail the write's clause. `subst_typed_var`
is the statement that survives that: the substituted term is a variable the term and the
environments do not already hold, so the substitution renames rather than duplicates, and
the environments are read at the renamed occurrences.
-/
import Scidonia.RC.Lower
import Scidonia.RC.Pure

namespace Scidonia.RC

/-! ## The traversals the rules read

Four traversals in the style of `uses`, each a structural recursion the kernel can
evaluate at a concrete term: whether a term writes the cell a name carries (`writes`),
whether a term is a node the program constructed (`BuiltB`), and the names a term
mentions (`vars`) and binds (`binds`), which the substitution below is read against.
`writes` and `BuiltB` are what the typing's two name conditions ask about. -/

/-- Whether `s` is the variable `x`: the subject test a write's traversal reads, and one
that a substitution by another name does not change. -/
def isVarB (x : Var) : Expr → Bool
  | .var y => decide (y = x)
  | _ => false

/-- Whether `e` writes the cell its free variable `x` carries: true at a write whose
subject is `var x`, stopped by a binder of `x` --- the shadowing `uses` reads, so a
write to an inner binder of the same name is not a write to `x`. A `dup` or a `drop`
node writes nothing, and neither is source syntax. -/
def writes (x : Var) : Expr → Bool
  | .var _ => false
  | .lam y body => if y = x then false else writes x body
  | .app f a => writes x f || writes x a
  | .bind y e₁ e₂ => writes x e₁ || (if y = x then false else writes x e₂)
  | .matchC s _ ys body => writes x s || (if x ∈ ys then false else writes x body)
  | .dup _ _ => false
  | .drop _ _ => false
  | .con0 _ => false
  | .con1 _ a => writes x a
  | .con2 _ a b => writes x a || writes x b
  | .store s _ v => isVarB x s || writes x s || writes x v

/-- Whether `e` is a node of the syntax: one of the three forms a node is written at,
a value the program constructs rather than a name for a cell it already holds. -/
def BuiltB : Expr → Bool
  | .var _ => false
  | .lam _ _ => false
  | .app _ _ => false
  | .bind _ _ _ => false
  | .matchC _ _ _ _ => false
  | .dup _ _ => false
  | .drop _ _ => false
  | .con0 _ => true
  | .con1 _ _ => true
  | .con2 _ _ _ => true
  | .store _ _ _ => false

/-- Every name `e` mentions, a binder's name included: the names a substitution has
to keep away from, and not the free occurrences `uses` counts. -/
def vars : Expr → List Var
  | .var x => [x]
  | .lam x body => x :: vars body
  | .app f a => vars f ++ vars a
  | .bind x e₁ e₂ => x :: (vars e₁ ++ vars e₂)
  | .matchC s _ ys body => vars s ++ ys ++ vars body
  | .dup x e => x :: vars e
  | .drop x e => x :: vars e
  | .con0 _ => []
  | .con1 _ a => vars a
  | .con2 _ a b => vars a ++ vars b
  | .store s _ v => vars s ++ vars v

/-- Whether `x` is one of the names `e` binds: the binder of an abstraction or of a
binding, or one of a matching arm's binders. -/
def binds (x : Var) : Expr → Bool
  | .var _ => false
  | .lam y body => if y = x then true else binds x body
  | .app f a => binds x f || binds x a
  | .bind y e₁ e₂ => if y = x then true else binds x e₁ || binds x e₂
  | .matchC s _ ys body => binds x s || (if x ∈ ys then true else binds x body)
  | .dup _ _ => false
  | .drop _ _ => false
  | .con0 _ => false
  | .con1 _ a => binds x a
  | .con2 _ a b => binds x a || binds x b
  | .store s _ v => binds x s || binds x v

/-! ## The typing

One rule per construct of the source, each over the canonical splits of
`Scidonia.RC.Lower`, with the write's clause strengthened to ownership and the rules
that bind a name carrying the two conditions a written name has to meet. -/

/-- The source term `e` is typed under the borrowed occurrences `Δ` and the owned
occurrences `Γ`: the lowering's environment discipline read as a typing, with a write's
subject required to be owned exactly once in its environment and not borrowed, and with
a name that a rule binds required to be used exactly once in its scope when its body
writes it, and required to be introduced for, or matched out of, a construction rather
than another name --- the bound term for a binding, the matched subject for an arm. The
environment is an index of the judgement and not a parameter of the rule's conclusion,
because a binder's body is typed at the environment the binder leaves (`forget Δ x`,
`bindEnv Γ x (uses body)`) and an arm's body at the arm's binders. -/
inductive Typed : Occs → Occs → Expr → Prop where
  /-- A variable is typed where an environment supplies it, owned or borrowed. -/
  | var {Δ Γ : Occs} {x : Var} (h : x ∈ Γ ∨ x ∈ Δ) : Typed Δ Γ (.var x)
  /-- An abstraction is typed when its body is, its name bound by the binder: the body
  is handed one owned occurrence of the binder's name beside the occurrences its other
  names claim, and if the body writes the binder's name the body uses it exactly
  once. -/
  | lam {Δ Γ : Occs} {x : Var} {body : Expr}
      (hlin : writes x body = true → (uses body).count x = 1)
      (h : Typed (forget Δ x) (bindEnv Γ x (uses body)) body) : Typed Δ Γ (.lam x body)
  /-- An application is typed when both positions are, the environment split between
  the occurrences the term's usage claims for them. -/
  | app {Δ Γ : Occs} {f a : Expr} (hf : Typed Δ (claimEnv Γ (uses f)) f)
      (ha : Typed Δ (claimEnv Γ (uses a)) a) : Typed Δ Γ (.app f a)
  /-- A binding is typed when its two terms are, the second handed one owned occurrence
  of the binder's name beside the occurrences its other names claim; if the second term
  writes the binder's name, that term uses the name exactly once and the first term is
  a construction the program built rather than another name. -/
  | bind {Δ Γ : Occs} {x : Var} {e₁ e₂ : Expr}
      (hlin : writes x e₂ = true → (uses e₂).count x = 1)
      (hbuild : writes x e₂ = true → BuiltB e₁ = true)
      (h₁ : Typed Δ (claimEnv Γ (uses e₁)) e₁)
      (h₂ : Typed (forget Δ x) (bindEnv Γ x (uses e₂)) e₂) : Typed Δ Γ (.bind x e₁ e₂)
  /-- A match is typed when its subject and its arm's body are, the arm handed one owned
  occurrence per binder beside the occurrences the body's other names claim; for each
  binder whose name the body writes, the body uses that name exactly once and the
  matched subject is a construction the program built rather than another name. -/
  | matchC {Δ Γ : Occs} {s : Expr} {c : Ctor} {ys : List Var} {body : Expr}
      (hlin : ∀ y ∈ ys, writes y body = true → (uses body).count y = 1)
      (hbuild : ∀ y ∈ ys, writes y body = true → BuiltB s = true)
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
  | lam hlin h ih => exact ih
  | app hf ha ihf iha => exact ⟨ihf, iha⟩
  | bind hlin hbuild h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | matchC hlin hbuild hs h ihs ih => exact ⟨ihs, ih⟩
  | con0 => trivial
  | con1 h ih => exact ih
  | con2 h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | store hown hborrow hv ihv => exact ⟨hown, hborrow, ihv⟩

/-! ## The name a write's subject carries

The two name conditions are statements about the term's syntax alone, and each is
carried by a traversal in the style of `WriteOwned`. -/

/-- Every binding rule of `e` whose body writes the name it binds uses that name
exactly once in the body it binds: the same recursion as the typing, asking at `lam`,
`bind` and each of an arm's binders the side condition the rule requires. -/
def WriteLinear : Expr → Prop
  | .var _ => True
  | .lam x body => (writes x body = true → (uses body).count x = 1) ∧ WriteLinear body
  | .app f a => WriteLinear f ∧ WriteLinear a
  | .bind x e₁ e₂ =>
      (writes x e₂ = true → (uses e₂).count x = 1) ∧ WriteLinear e₁ ∧ WriteLinear e₂
  | .matchC s _ ys body =>
      (∀ y ∈ ys, writes y body = true → (uses body).count y = 1)
        ∧ WriteLinear s ∧ WriteLinear body
  | .dup _ _ => True
  | .drop _ _ => True
  | .con0 _ => True
  | .con1 _ a => WriteLinear a
  | .con2 _ a b => WriteLinear a ∧ WriteLinear b
  | .store _ _ v => WriteLinear v

/-- Every binding rule of `e` whose body writes the name it binds introduces that name
for a construction of the program --- the bound term for a binding, the matched subject
for an arm: the same recursion as the typing, asking at `bind` and each of an arm's
binders the second side condition the rule requires. -/
def WriteBuilt : Expr → Prop
  | .var _ => True
  | .lam _ body => WriteBuilt body
  | .app f a => WriteBuilt f ∧ WriteBuilt a
  | .bind x e₁ e₂ =>
      (writes x e₂ = true → BuiltB e₁ = true) ∧ WriteBuilt e₁ ∧ WriteBuilt e₂
  | .matchC s _ ys body =>
      (∀ y ∈ ys, writes y body = true → BuiltB s = true) ∧ WriteBuilt s ∧ WriteBuilt body
  | .dup _ _ => True
  | .drop _ _ => True
  | .con0 _ => True
  | .con1 _ a => WriteBuilt a
  | .con2 _ a b => WriteBuilt a ∧ WriteBuilt b
  | .store _ _ v => WriteBuilt v

/-- A typed term has every binding rule whose body writes the name it binds use that
name exactly once in the body it binds: the rules' first name condition, carried by the
traversal `WriteLinear`. -/
theorem typed_write_linear {Δ Γ : Occs} {e : Expr} (h : Typed Δ Γ e) :
    WriteLinear e := by
  induction h with
  | var h => trivial
  | lam hlin h ih => exact ⟨hlin, ih⟩
  | app hf ha ihf iha => exact ⟨ihf, iha⟩
  | bind hlin hbuild h₁ h₂ ih₁ ih₂ => exact ⟨hlin, ih₁, ih₂⟩
  | matchC hlin hbuild hs h ihs ih => exact ⟨hlin, ihs, ih⟩
  | con0 => trivial
  | con1 h ih => exact ih
  | con2 h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | store hown hborrow hv ihv => exact ihv

/-- A typed term has every binding rule whose body writes the name it binds introduce
that name for a construction of the program --- the bound term for a binding, the
matched subject for an arm: the rules' second name condition, carried by the traversal
`WriteBuilt`. -/
theorem typed_write_built {Δ Γ : Occs} {e : Expr} (h : Typed Δ Γ e) : WriteBuilt e := by
  induction h with
  | var h => trivial
  | lam hlin h ih => exact ih
  | app hf ha ihf iha => exact ⟨ihf, iha⟩
  | bind hlin hbuild h₁ h₂ ih₁ ih₂ => exact ⟨hbuild, ih₁, ih₂⟩
  | matchC hlin hbuild hs h ihs ih => exact ⟨hbuild, ihs, ih⟩
  | con0 => trivial
  | con1 h ih => exact ih
  | con2 h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | store hown hborrow hv ihv => exact ihv

/-- A name bound by an abstraction whose body writes it is used exactly once in that
body: the abstraction rule's own reading of the first name condition. -/
theorem typed_lam_written_linear {Δ Γ : Occs} {x : Var} {body : Expr}
    (h : Typed Δ Γ (.lam x body)) (hw : writes x body = true) : (uses body).count x = 1 := by
  cases h with
  | lam hlin _ => exact hlin hw

/-- A name bound by a binding whose body writes it is used exactly once in that body:
the binding rule's own reading of the first name condition. -/
theorem typed_bind_written_linear {Δ Γ : Occs} {x : Var} {e₁ e₂ : Expr}
    (h : Typed Δ Γ (.bind x e₁ e₂)) (hw : writes x e₂ = true) : (uses e₂).count x = 1 := by
  cases h with
  | bind hlin _ _ _ => exact hlin hw

/-- An arm's binder whose name the arm's body writes is used exactly once in that body:
the arm rule's own reading of the first name condition. -/
theorem typed_arm_written_linear {Δ Γ : Occs} {s : Expr} {c : Ctor} {ys : List Var}
    {body : Expr} (h : Typed Δ Γ (.matchC s c ys body)) {y : Var} (hy : y ∈ ys)
    (hw : writes y body = true) : (uses body).count y = 1 := by
  cases h with
  | matchC hlin _ _ _ => exact hlin y hy hw

/-- A name bound by a binding whose body writes it is bound to a construction of the
program: the binding rule's own reading of the second name condition. -/
theorem typed_bind_written_built {Δ Γ : Occs} {x : Var} {e₁ e₂ : Expr}
    (h : Typed Δ Γ (.bind x e₁ e₂)) (hw : writes x e₂ = true) : BuiltB e₁ = true := by
  cases h with
  | bind _ hbuild _ _ => exact hbuild hw

/-- An arm's binder whose name the arm's body writes is matched out of a construction of
the program: the arm rule's own reading of the second name condition. -/
theorem typed_arm_written_built {Δ Γ : Occs} {s : Expr} {c : Ctor} {ys : List Var}
    {body : Expr} (h : Typed Δ Γ (.matchC s c ys body)) {y : Var} (hy : y ∈ ys)
    (hw : writes y body = true) : BuiltB s = true := by
  cases h with
  | matchC _ hbuild _ _ => exact hbuild y hy hw

/-- A name bound by a binding whose body writes it is bound to a construction of the
program and used exactly once in that body: two source-level facts of the term --- the
program builds the cell the write lands at, and the term names it once --- and not a
count on the target heap. -/
theorem typed_bind_written_own {Δ Γ : Occs} {x : Var} {e₁ e₂ : Expr}
    (h : Typed Δ Γ (.bind x e₁ e₂)) (hw : writes x e₂ = true) :
    BuiltB e₁ = true ∧ (uses e₂).count x = 1 :=
  ⟨typed_bind_written_built h hw, typed_bind_written_linear h hw⟩

/-- An arm's binder whose name the arm's body writes is matched out of a subject the
program built, and is used exactly once in that body: two source-level facts of the arm
--- the matched subject is a construction of the program, and the arm's body names its
binder once --- and not a count on the target heap. The binder names a *field* of that
subject, and a field that is itself a name is the case the caveat above leaves outside
the guarantees. -/
theorem typed_arm_written_own {Δ Γ : Occs} {s : Expr} {c : Ctor} {ys : List Var}
    {body : Expr} (h : Typed Δ Γ (.matchC s c ys body)) {y : Var} (hy : y ∈ ys)
    (hw : writes y body = true) : BuiltB s = true ∧ (uses body).count y = 1 :=
  ⟨typed_arm_written_built h hy hw, typed_arm_written_linear h hy hw⟩

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
typing's splits are the lowering's, so the typing's derivation is a lowering's, and the
rules' name conditions are about the term and not about the target. -/
theorem typed_lowers {Δ Γ : Occs} {e : Expr} (h : Typed Δ Γ e) : ∃ e', Lower Δ Γ e e' := by
  induction h with
  | var h => exact ⟨_, Lower.var h⟩
  | lam hlin h ih =>
      obtain ⟨body', hb⟩ := ih
      exact ⟨_, Lower.lam hb⟩
  | app hf ha ihf iha =>
      obtain ⟨f', hf'⟩ := ihf
      obtain ⟨a', ha'⟩ := iha
      exact ⟨_, Lower.app hf' ha'⟩
  | bind hlin hbuild h₁ h₂ ih₁ ih₂ =>
      obtain ⟨e₁', h₁'⟩ := ih₁
      obtain ⟨e₂', h₂'⟩ := ih₂
      exact ⟨_, Lower.bind h₁' h₂'⟩
  | matchC hlin hbuild hs h ihs ih =>
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

The write's clause and the two name conditions are statements about the term, not only
about the label the environment gives it: a program that writes to a name and also uses
that name fails them, and one that writes to a name it uses once meets them. The chosen
programs are closed, so their typing is read at the empty environments. -/

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

/-- The program that binds `0`, writes slot `0` of the cell `0` names, and also uses
`0` in a sibling position: the store's own occurrence is the subject's, so the write's
clause is met, and the *program* holds the cell twice. The first name condition is what
refuses it. -/
def siblingUse : Expr := .lam 0 (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.var 0)))

/-- The same program with the sibling's second reference replaced by a node: it writes
the cell and does not use it elsewhere, so the body uses the name once. -/
def siblingOwned : Expr := .lam 0 (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.con0 10)))

/-- The program that binds `0` to the *name* `1` and writes through the binding: the
written name is a second name for a cell the program already holds. The second name
condition is what refuses it. -/
def aliasBind : Expr := .bind 0 (.var 1) (.store (.var 0) 0 (.con0 9))

/-- The same program with the binding a construction: the written name is one the
program built. -/
def builtBind : Expr := .bind 0 (.con1 5 (.con0 5)) (.store (.var 0) 0 (.con0 9))

/-- The program whose write's subject is also the written value has no typing: the
store's environment carries two occurrences of `0`, and the write's clause asks for one.
`ScidoniaTest/Typing` reads the same statement and its disciplined control. -/
theorem dupValue_no_typing : ¬ Typed [] [] dupValue := by
  intro h
  unfold dupValue at h
  cases h with
  | lam hlin h => cases h with
    | con1 h => cases h with
      | store hown => exact absurd hown (by decide)

/-- A program whose arm binds the write's subject twice has no typing: the arm's binder
list supplies the name twice, and the write's clause asks for one occurrence. This is
the duplication at the binder list rather than at the written value. -/
theorem dupArm_no_typing : ¬ Typed [] [] dupArm := by
  intro h
  unfold dupArm at h
  cases h with
  | matchC _ _ _ h => cases h with
    | store hown => exact absurd hown (by decide)

/-- The disciplined program is typed: the write's subject is used once, as the
subject. -/
theorem ownedValue_typed : Typed [] [] ownedValue := by
  unfold ownedValue
  refine Typed.lam (x := 0) (by decide) ?_
  refine Typed.con1 ?_
  refine Typed.store (by decide) (by decide) ?_
  exact Typed.con0

/-- The disciplined arm program is typed: the arm binds the write's subject once. -/
theorem ownedArm_typed : Typed [] [] ownedArm := by
  unfold ownedArm
  refine Typed.matchC (ys := [0]) ?_ ?_ ?_ ?_
  · intro y hy
    simp at hy
    subst hy
    decide
  · intro y hy
    simp at hy
    subst hy
    intro _
    rfl
  · refine Typed.con1 ?_
    exact Typed.con0
  · refine Typed.store (by decide) (by decide) ?_
    exact Typed.con0

/-- The program that uses the write's subject in a sibling position has no typing: the
body writes `0` and uses it twice, so the abstraction rule's name condition refuses it.
The store's own clause is met --- the sibling's use is not counted at the store --- and
this is the refutation that the store's own environment alone cannot give. -/
theorem sibling_use_no_typing : ¬ Typed [] [] siblingUse := by
  intro h
  unfold siblingUse at h
  cases h with
  | lam hlin _ =>
      have hw : writes 0 (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.var 0))) = true :=
        by decide
      have h1 : (uses (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.var 0)))).count 0 = 1 :=
        hlin hw
      have h2 : (uses (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.var 0)))).count 0 = 2 :=
        by decide
      omega

/-- The counterpart of the refutation above: the program writes the cell `0` names and
does not use `0` elsewhere, so the abstraction rule's name condition is met and the
program is typed. -/
theorem sibling_use_owned : Typed [] [] siblingOwned := by
  unfold siblingOwned
  refine Typed.lam (x := 0) (by decide) ?_
  refine Typed.con1 ?_
  refine Typed.con2 ?_ ?_
  · refine Typed.store (by decide) (by decide) ?_
    exact Typed.con0
  · exact Typed.con0

/-- A program that binds a name to another name and writes through the binding has no
typing: the binding rule's second name condition asks the bound term to be a
construction, and a variable is none. The refutation is at every environment, because
the condition is a statement about the term. -/
theorem alias_bind_no_typing {Δ Γ : Occs} {x z : Var} {i : Nat} {v : Expr} :
    ¬ Typed Δ Γ (.bind x (.var z) (.store (.var x) i v)) := by
  intro h
  cases h with
  | bind _ hbuild _ _ =>
      have hw : writes x (.store (.var x) i v) = true := by simp [writes, isVarB]
      have hbuilt := hbuild hw
      exact Bool.false_ne_true hbuilt

/-- The counterpart of the refutation above: the same program with the binding a
construction is typed. The name condition is met because the written name is bound to a
node the program built. -/
theorem built_bind_typed : Typed [] [] builtBind := by
  unfold builtBind
  refine Typed.bind (x := 0) (by decide) ?_ ?_ ?_
  · intro _
    rfl
  · refine Typed.con1 ?_
    exact Typed.con0
  · refine Typed.store (by decide) (by decide) ?_
    exact Typed.con0

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

The other half --- that a typed term's *environments* survive a step --- is
`subst_typed_var` below, under the restriction that the substituted term is a variable
the term and the environments do not already hold; the section above states the
counterexample that makes the restriction necessary. -/

/-- A typed term is a term of the source fragment: the typing has no rule for a `dup`
or a `drop`, so a typed term mentions neither. -/
theorem typed_pure {Δ Γ : Occs} {e : Expr} (h : Typed Δ Γ e) : Pure e := by
  induction h with
  | var h => exact Pure.var _
  | lam hlin h ih => exact Pure.lam ih
  | app hf ha ihf iha => exact Pure.app ihf iha
  | bind hlin hbuild h₁ h₂ ih₁ ih₂ => exact Pure.bind ih₁ ih₂
  | matchC hlin hbuild hs h ihs ih => exact Pure.matchC ihs ih
  | con0 => exact Pure.con0 _
  | con1 h ih => exact Pure.con1 ih
  | con2 h₁ h₂ ih₁ ih₂ => exact Pure.con2 ih₁ ih₂
  | store hown hborrow hv ihv => exact Pure.store (Pure.var _) ihv

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

/-! ## Survival of the typing under substitution

A substitution replaces a name by a variable, and the environments have to be read at
the renamed name: `rename x y` sends `x` to `y` and every other name to itself, so
`Γ.map (rename x y)` is the environment whose `x`'s are its `y`'s. The facts below are
what the typing's splits do under that map, and each needs the substitute to be a name
neither the term nor the environments hold: a name the environments hold on both sides
of the renaming is exactly the duplication the same-environment statement cannot
survive. -/

/-- The renaming a substitution by the variable `y` for `x` applies to a name: `x`
becomes `y`, and every other name stands. -/
def rename (x y : Var) : Var → Var := fun z => if z = x then y else z

/-- A renaming sends the name it renames to its image. -/
@[simp] theorem rename_self (x y : Var) : rename x y x = y := by simp [rename]

/-- A renaming leaves every other name alone. -/
@[simp] theorem rename_of_ne {x y z : Var} (h : z ≠ x) : rename x y z = z := by
  simp [rename, h]

/-- A renaming's own image stands: the only name it moves is the one it renames. -/
@[simp] theorem rename_image (x y : Var) : rename x y y = y := by
  by_cases h : y = x
  · rw [h, rename_self]
  · exact rename_of_ne h

/-- A renaming's image is either the renamed name or its own image: no third name is
sent to `y`. -/
theorem rename_eq_image {x y z : Var} (h : rename x y z = y) : z = x ∨ z = y := by
  by_cases hzx : z = x
  · exact Or.inl hzx
  · rw [rename_of_ne hzx] at h
    exact Or.inr h

/-- A renaming moves a name to a name it does not move exactly when the name was
already there: the only two names a renaming changes are `x` and `y`. -/
theorem rename_eq_iff {x y z w : Var} (hw : w ≠ x) (hwy : w ≠ y) :
    rename x y z = w ↔ z = w := by
  constructor
  · intro h
    by_cases hzx : z = x
    · rw [hzx, rename_self] at h
      exact absurd h.symm hwy
    · rwa [rename_of_ne hzx] at h
  · intro h
    rw [h, rename_of_ne hw]

/-- A list all of whose names differ from the renamed name stands under the renaming. -/
theorem map_rename_of_ne {x y : Var} : ∀ {l : List Var}, (∀ z ∈ l, z ≠ x) → l.map (rename x y) = l
  | [], _ => rfl
  | z :: l, h => by
      have hz : z ≠ x := h z (by simp)
      have hl : ∀ w ∈ l, w ≠ x := fun w hw => h w (by simp [hw])
      simp [rename_of_ne hz, map_rename_of_ne hl]

/-- A list of names the renaming does not move stands under it. -/
theorem map_rename_list {x y : Var} {ys : List Var} (hx : x ∉ ys) : ys.map (rename x y) = ys :=
  map_rename_of_ne (fun _ hz hzx => hx (hzx ▸ hz))

/-- A name stands in a list of names the renaming does not move. -/
theorem mem_map_rename_iff {x y a : Var} {ys : List Var} (hx : x ∉ ys) (hy : y ∉ ys) :
    rename x y a ∈ ys ↔ a ∈ ys := by
  constructor
  · intro h
    by_cases hax : a = x
    · rw [hax] at h
      rw [rename_self] at h
      exact absurd h hy
    · rwa [rename_of_ne hax] at h
  · intro h
    by_cases hax : a = x
    · rw [hax] at h ⊢
      rw [rename_self]
      exact absurd h hx
    · rwa [rename_of_ne hax]

/-- A name is an image of the renamed environment exactly when the environment holds
it: the renaming moves `x` to `y` and nothing else, so a name the environment does not
hold cannot appear in its image. -/
theorem rename_mem_map {x y a : Var} {Γ : Occs} (hyΓ : y ∉ Γ) (hay : a ≠ y) :
    rename x y a ∈ Γ.map (rename x y) ↔ a ∈ Γ := by
  constructor
  · intro h
    obtain ⟨u, hu, hueq⟩ := List.mem_map.mp h
    have hua : u = a := by
      by_cases hax : a = x
      · rw [hax] at hueq
        rw [rename_self] at hueq
        rcases rename_eq_image hueq with hux | huy
        · rw [hux, hax]
        · exact absurd (huy ▸ hu) hyΓ
      · rw [rename_of_ne hax] at hueq
        by_cases hux : u = x
        · rw [hux, rename_self] at hueq
          exact absurd hueq.symm hay
        · rw [rename_of_ne hux] at hueq
          exact hueq
    rwa [hua] at hu
  · intro h
    exact List.mem_map.mpr ⟨a, h, rfl⟩

/-- Mapping a list and filtering the image agrees with filtering by the test pulled back
along the mapping and mapping: filtering commutes with a mapping when the two tests
agree on the image of every element of the list. -/
theorem map_filter_map (l : List Var) (σ : Var → Var) (p q : Var → Bool)
    (h : ∀ a ∈ l, p (σ a) = q a) : (l.map σ).filter p = (l.filter q).map σ := by
  rw [List.filter_map]
  exact congrArg (List.map σ) (List.filter_congr h)

/-- Counting a name the renaming does not move is counting it before the renaming: the
only occurrences the renaming moves are the renamed name's. -/
theorem count_map_rename_of_ne {Γ : Occs} {x y z : Var} (hzx : z ≠ x) (hzy : z ≠ y) :
    (Γ.map (rename x y)).count z = Γ.count z := by
  induction Γ with
  | nil => rfl
  | cons u Γ ih =>
      rw [List.map_cons, List.count_cons, List.count_cons, ih]
      have h : (rename x y u == z) = (u == z) := by
        change decide (rename x y u = z) = decide (u = z)
        rw [decide_eq_decide]
        exact rename_eq_iff hzx hzy
      rw [h]

/-- Counting the renaming's image is counting both names it moves: the occurrences sent
to `y` are the renamed name's and the image's own. -/
theorem count_map_rename_image {Γ : Occs} {x y : Var} (hxy : x ≠ y) :
    (Γ.map (rename x y)).count y = Γ.count x + Γ.count y := by
  have hself : ∀ a : Var, (a == a) = true := by
    intro a
    rw [show (a == a) = decide (a = a) from rfl]
    exact decide_eq_true rfl
  have hne : ∀ a b : Var, a ≠ b → ((a == b) = true → False) := by
    intro a b hab h
    rw [show (a == b) = decide (a = b) from rfl] at h
    exact hab (of_decide_eq_true h)
  induction Γ with
  | nil => rfl
  | cons u Γ ih =>
      rw [List.map_cons, List.count_cons, List.count_cons, List.count_cons, ih]
      by_cases hux : u = x
      · rw [hux, rename_self, ite_eq_left (hself y), ite_eq_left (hself x), ite_eq_right (hne x y hxy)]
        omega
      · by_cases huy : u = y
        · rw [huy, rename_image, ite_eq_left (hself y), ite_eq_right (hne y x (Ne.symm hxy))]
          omega
        · rw [rename_of_ne hux, ite_eq_right (hne u y huy), ite_eq_right (hne u x hux)]
          omega

/-- Claiming occurrences from a renamed environment is claiming them and renaming: a
claim is a membership filter, and the renaming moves only its two names. -/
theorem claimEnv_map {Γ : Occs} {u : List Var} {x y : Var} (hyu : y ∉ u) (hyΓ : y ∉ Γ) :
    claimEnv (Γ.map (rename x y)) (u.map (rename x y)) = (claimEnv Γ u).map (rename x y) := by
  rw [claimEnv, claimEnv]
  exact map_filter_map u (rename x y) (fun v => v ∈ Γ.map (rename x y)) (fun a => a ∈ Γ)
    (fun a ha => by
      change decide (rename x y a ∈ Γ.map (rename x y)) = decide (a ∈ Γ)
      rw [decide_eq_decide]
      exact rename_mem_map hyΓ (fun hay => hyu (hay ▸ ha)))

/-- A name the environment does not hold is not claimed by any usage: a claim is a
membership filter of the environment. -/
theorem not_mem_claimEnv {Γ : Occs} {u : List Var} {y : Var} (h : y ∉ Γ) : y ∉ claimEnv Γ u := by
  intro hh
  have hh' : y ∈ u ∧ y ∈ Γ := by simpa [claimEnv] using hh
  exact h hh'.2

/-- Forgetting the binder's name commutes with the renaming, for a binder the renaming
does not move. -/
theorem forget_map {Δ : Occs} {x y w : Var} (hwx : w ≠ x) (hwy : w ≠ y) :
    forget (Δ.map (rename x y)) w = (forget Δ w).map (rename x y) := by
  rw [forget, forget]
  exact map_filter_map Δ (rename x y) (fun v => v ≠ w) (fun a => a ≠ w)
    (fun _ _ => by
      change decide (rename x y _ ≠ w) = decide (_ ≠ w)
      rw [decide_eq_decide]
      exact not_congr (rename_eq_iff hwx hwy))

/-- Forgetting a list of names commutes with the renaming, for binders the renaming does
not move. -/
theorem forgetAll_map {Δ : Occs} {ys : List Var} {x y : Var} (hx : x ∉ ys) (hy : y ∉ ys) :
    forgetAll (Δ.map (rename x y)) ys = (forgetAll Δ ys).map (rename x y) := by
  rw [forgetAll, forgetAll]
  exact map_filter_map Δ (rename x y) (fun v => v ∉ ys) (fun a => a ∉ ys)
    (fun _ _ => by
      change decide (rename x y _ ∉ ys) = decide (_ ∉ ys)
      rw [decide_eq_decide]
      exact not_congr (mem_map_rename_iff hx hy))

/-- The occurrences a binding hands its body commute with the renaming: the binder's own
occurrence is the renamed name's, so it is the image on the renamed environment. -/
theorem bindEnv_map {Γ : Occs} {u : List Var} {x y w : Var} (hwx : w ≠ x) (hwy : w ≠ y)
    (hyu : y ∉ u) (hyΓ : y ∉ Γ) :
    bindEnv (Γ.map (rename x y)) w (u.map (rename x y)) =
      (bindEnv Γ w u).map (rename x y) := by
  rw [bindEnv, bindEnv]
  simp only [List.map_cons, List.cons_append, List.nil_append, rename_of_ne hwx]
  rw [map_filter_map u (rename x y)
    (fun v => v ∈ Γ.map (rename x y) ∧ v ≠ w) (fun a => a ∈ Γ ∧ a ≠ w)
    (fun a ha => by
      change decide (rename x y a ∈ Γ.map (rename x y) ∧ rename x y a ≠ w)
        = decide (a ∈ Γ ∧ a ≠ w)
      rw [decide_eq_decide]
      exact and_congr (rename_mem_map hyΓ (fun hay => hyu (hay ▸ ha)))
        (not_congr (rename_eq_iff hwx hwy)))]

/-- The occurrences an arm hands its body commute with the renaming, for binders the
renaming does not move. -/
theorem armEnv_map {Γ : Occs} {ys : List Var} {u : List Var} {x y : Var} (hx : x ∉ ys)
    (hy : y ∉ ys) (hyu : y ∉ u) (hyΓ : y ∉ Γ) :
    armEnv (Γ.map (rename x y)) ys (u.map (rename x y)) = (armEnv Γ ys u).map (rename x y) := by
  rw [armEnv, armEnv, List.map_append, map_rename_list hx]
  rw [map_filter_map u (rename x y)
    (fun v => v ∈ Γ.map (rename x y) ∧ v ∉ ys) (fun a => a ∈ Γ ∧ a ∉ ys)
    (fun a ha => by
      change decide (rename x y a ∈ Γ.map (rename x y) ∧ rename x y a ∉ ys)
        = decide (a ∈ Γ ∧ a ∉ ys)
      rw [decide_eq_decide]
      exact and_congr (rename_mem_map hyΓ (fun hay => hyu (hay ▸ ha)))
        (not_congr (mem_map_rename_iff hx hy)))]

/-! ## What a substitution does to a term's names

A substitution's laws below are all read against the same restriction: the substitute is
a name the term does not mention and the environments do not hold. -/

/-- A free occurrence is a mention: the names `uses` counts are among the names `vars`
collects, so a name a term does not mention it does not use freely. -/
theorem mem_vars_of_mem_uses (e : Expr) : ∀ {x : Var}, x ∈ uses e → x ∈ vars e := by
  induction e with
  | var z => intro x h; simpa [uses, vars] using h
  | lam w body ih =>
      intro x h
      rw [uses] at h
      exact List.mem_cons.mpr (Or.inr (ih (List.mem_filter.mp h).1))
  | app f a ihf iha =>
      intro x h
      rw [uses] at h
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append.mpr (Or.inl (ihf h))
      · exact List.mem_append.mpr (Or.inr (iha h))
  | bind w e₁ e₂ ih₁ ih₂ =>
      intro x h
      rw [uses] at h
      rcases List.mem_append.mp h with h | h
      · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (ih₁ h))))
      · exact List.mem_cons.mpr
          (Or.inr (List.mem_append.mpr (Or.inr (ih₂ (List.mem_filter.mp h).1))))
  | matchC s c ys body ihs ihb =>
      intro x h
      rw [uses] at h
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (ihs h))))
      · exact List.mem_append.mpr (Or.inr (ihb (List.mem_filter.mp h).1))
  | dup w ex ih =>
      intro x h
      rw [uses] at h
      exact List.mem_cons.mpr ((List.mem_cons.mp h).elim Or.inl (fun h' => Or.inr (ih h')))
  | drop w ex ih =>
      intro x h
      rw [uses] at h
      exact List.mem_cons.mpr ((List.mem_cons.mp h).elim Or.inl (fun h' => Or.inr (ih h')))
  | con0 c => intro x h; simp [uses] at h
  | con1 c a iha => intro x h; rw [uses] at h; exact iha h
  | con2 c a b iha ihb =>
      intro x h
      rw [uses] at h
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append.mpr (Or.inl (iha h))
      · exact List.mem_append.mpr (Or.inr (ihb h))
  | store s i v ihs ihv =>
      intro x h
      rw [uses] at h
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append.mpr (Or.inl (ihs h))
      · exact List.mem_append.mpr (Or.inr (ihv h))

/-- A substitution by another name does not change whether a term's subject position is
the variable a write's traversal reads: the substitution either leaves the subject a
variable of the substituted name's image, which is not the one asked about, or leaves the
subject a term that is not a variable. -/
theorem isVarB_subst (s : Expr) : ∀ {x y z : Var}, z ≠ x → z ≠ y →
    isVarB z (subst x (.var y) s) = isVarB z s := by
  induction s with
  | var u =>
      intro x y z hzx hzy
      by_cases hux : u = x
      · subst hux
        simp [subst_var_self, isVarB, Ne.symm hzx, Ne.symm hzy]
      · rw [subst_var_of_ne hux]
  | lam w body ih => intro x y z hzx hzy; rw [subst]; split <;> rfl
  | app f a ihf iha => intro x y z hzx hzy; rfl
  | bind w e₁ e₂ ih₁ ih₂ => intro x y z hzx hzy; rfl
  | matchC s c ys body ihs ihb => intro x y z hzx hzy; rfl
  | dup w ex ih => intro x y z hzx hzy; rfl
  | drop w ex ih => intro x y z hzx hzy; rfl
  | con0 c => intro x y z hzx hzy; rfl
  | con1 c a iha => intro x y z hzx hzy; rfl
  | con2 c a b iha ihb => intro x y z hzx hzy; rfl
  | store s i v ihs ihv => intro x y z hzx hzy; rfl

/-- The free occurrences of a substitution by a fresh variable: the term's occurrences
with the substituted name renamed. The freshness is what makes the law hold --- the
substitute is a name the term does not mention, so no binder of the term captures it ---
and purity is what the traversal reads: `uses` counts a `dup` or a `drop` node's name,
and `subst` inserts nothing for it. -/
theorem uses_subst_var (e : Expr) : ∀ {x y : Var}, Pure e → y ∉ vars e →
    uses (subst x (.var y) e) = (uses e).map (rename x y) := by
  induction e with
  | var z =>
      intro x y _ hy
      by_cases hzx : z = x
      · subst hzx
        simp [subst_var_self, uses, rename_self]
      · rw [subst_var_of_ne hzx]
        simp only [uses, List.map_cons, List.map_nil]
        rw [rename_of_ne hzx]
  | lam w body ih =>
      intro x y hp hy
      have hpb : Pure body := (pure_lam_iff w body).mp hp
      have hyw : y ≠ w := fun h => hy (List.mem_cons.mpr (Or.inl h))
      have hyb : y ∉ vars body := fun h => hy (List.mem_cons.mpr (Or.inr h))
      by_cases hwx : w = x
      · subst hwx
        rw [subst, ite_eq_left rfl]
        simp only [uses]
        refine (map_rename_of_ne (fun z hz hzx => ?_)).symm
        have hzz : z ≠ w := by
          have hh := hz
          simp only [List.mem_filter, decide_eq_true_eq] at hh
          exact hh.2
        exact hzz hzx
      · rw [subst, ite_eq_right hwx]
        simp only [uses]
        rw [ih hpb hyb]
        rw [map_filter_map (uses body) (rename x y) (fun z => z ≠ w) (fun z => z ≠ w)
          (fun a _ => by
            change decide (rename x y a ≠ w) = decide (a ≠ w)
            rw [decide_eq_decide]
            exact not_congr (rename_eq_iff hwx (Ne.symm hyw)))]
  | app f a ihf iha =>
      intro x y hp hy
      obtain ⟨hpf, hpa⟩ := (pure_app_iff f a).mp hp
      have hyf : y ∉ vars f := fun h => hy (List.mem_append.mpr (Or.inl h))
      have hya : y ∉ vars a := fun h => hy (List.mem_append.mpr (Or.inr h))
      rw [subst]
      simp only [uses, List.map_append]
      rw [ihf hpf hyf, iha hpa hya]
  | bind w e₁ e₂ ih₁ ih₂ =>
      intro x y hp hy
      obtain ⟨hp₁, hp₂⟩ := (pure_bind_iff w e₁ e₂).mp hp
      have hyw : y ≠ w := fun h => hy (List.mem_cons.mpr (Or.inl h))
      have hy1 : y ∉ vars e₁ := fun h =>
        hy (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h))))
      have hy2 : y ∉ vars e₂ := fun h =>
        hy (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h))))
      by_cases hwx : w = x
      · subst hwx
        rw [subst, ite_eq_left rfl]
        simp only [uses, List.map_append]
        rw [ih₁ hp₁ hy1]
        congr 1
        refine (map_rename_of_ne (fun z hz hzx => ?_)).symm
        have hzz : z ≠ w := by
          have hh := hz
          simp only [List.mem_filter, decide_eq_true_eq] at hh
          exact hh.2
        exact hzz hzx
      · rw [subst, ite_eq_right hwx]
        simp only [uses, List.map_append]
        rw [ih₁ hp₁ hy1, ih₂ hp₂ hy2]
        rw [map_filter_map (uses e₂) (rename x y) (fun z => z ≠ w) (fun z => z ≠ w)
          (fun a _ => by
            change decide (rename x y a ≠ w) = decide (a ≠ w)
            rw [decide_eq_decide]
            exact not_congr (rename_eq_iff hwx (Ne.symm hyw)))]
  | matchC s c ys body ihs ihb =>
      intro x y hp hy
      obtain ⟨hps, hpb⟩ := (pure_matchC_iff s c ys body).mp hp
      have hys : y ∉ vars s := fun h =>
        hy (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h))))
      have hyys : y ∉ ys := fun h =>
        hy (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h))))
      have hyb : y ∉ vars body := fun h => hy (List.mem_append.mpr (Or.inr h))
      by_cases hxys : x ∈ ys
      · rw [subst, ite_eq_left hxys]
        simp only [uses, List.map_append]
        rw [ihs hps hys]
        congr 1
        refine (map_rename_of_ne (fun z hz hzx => ?_)).symm
        have hzz : z ∉ ys := by
          have hh := hz
          simp only [List.mem_filter, decide_eq_true_eq] at hh
          exact hh.2
        exact hzz (hzx ▸ hxys)
      · rw [subst, ite_eq_right hxys]
        simp only [uses, List.map_append]
        rw [ihs hps hys, ihb hpb hyb]
        rw [map_filter_map (uses body) (rename x y) (fun z => z ∉ ys) (fun z => z ∉ ys)
          (fun a _ => by
            change decide (rename x y a ∉ ys) = decide (a ∉ ys)
            rw [decide_eq_decide]
            exact not_congr (mem_map_rename_iff hxys hyys))]
  | dup w ex _ => intro x y hp _; exact absurd hp (not_pure_dup w ex)
  | drop w ex _ => intro x y hp _; exact absurd hp (not_pure_drop w ex)
  | con0 c => intro x y _ _; simp [subst, uses]
  | con1 c a iha =>
      intro x y hp hy
      have hpa : Pure a := (pure_con1_iff c a).mp hp
      rw [subst]
      simp only [uses]
      exact iha hpa hy
  | con2 c a b iha ihb =>
      intro x y hp hy
      obtain ⟨hpa, hpb⟩ := (pure_con2_iff c a b).mp hp
      have hya : y ∉ vars a := fun h => hy (List.mem_append.mpr (Or.inl h))
      have hyb : y ∉ vars b := fun h => hy (List.mem_append.mpr (Or.inr h))
      rw [subst]
      simp only [uses, List.map_append]
      rw [iha hpa hya, ihb hpb hyb]
  | store s i v ihs ihv =>
      intro x y hp hy
      obtain ⟨hps, hpv⟩ := (pure_store_iff s i v).mp hp
      have hys : y ∉ vars s := fun h => hy (List.mem_append.mpr (Or.inl h))
      have hyv : y ∉ vars v := fun h => hy (List.mem_append.mpr (Or.inr h))
      rw [subst]
      simp only [uses, List.map_append]
      rw [ihs hps hys, ihv hpv hyv]

/-- Whether a term writes a name other than the two a substitution moves is unchanged by
the substitution: the substitute is a variable, so the substitution writes nothing new,
and the renamed name is not the one the traversal asks about. -/
theorem writes_subst_var (e : Expr) : ∀ {x y z : Var}, z ≠ x → z ≠ y →
    writes z (subst x (.var y) e) = writes z e := by
  induction e with
  | var u =>
      intro x y z hzx hzy
      by_cases hux : u = x
      · simp [hux, subst_var_self, writes]
      · simp [subst_var_of_ne hux, writes]
  | lam w body ih =>
      intro x y z hzx hzy
      by_cases hwx : w = x
      · rw [hwx] at *
        rw [subst, ite_eq_left rfl]
      · rw [subst, ite_eq_right hwx]
        simp only [writes]
        rw [ih hzx hzy]
  | app f a ihf iha =>
      intro x y z hzx hzy
      rw [subst]
      simp only [writes]
      rw [ihf hzx hzy, iha hzx hzy]
  | bind w e₁ e₂ ih₁ ih₂ =>
      intro x y z hzx hzy
      by_cases hwx : w = x
      · rw [hwx] at *
        rw [subst, ite_eq_left rfl]
        simp only [writes]
        rw [ih₁ hzx hzy]
      · rw [subst, ite_eq_right hwx]
        simp only [writes]
        rw [ih₁ hzx hzy, ih₂ hzx hzy]
  | matchC s c ys body ihs ihb =>
      intro x y z hzx hzy
      rw [subst]
      by_cases hxys : x ∈ ys
      · rw [ite_eq_left hxys]
        simp only [writes]
        rw [ihs hzx hzy]
      · rw [ite_eq_right hxys]
        simp only [writes]
        rw [ihs hzx hzy]
        by_cases hzys : z ∈ ys
        · simp [hzys]
        · simp [hzys, ihb hzx hzy]
  | dup w ex _ => intro x y z hzx hzy; simp [subst, writes]
  | drop w ex _ => intro x y z hzx hzy; simp [subst, writes]
  | con0 c => intro x y z hzx hzy; simp [subst, writes]
  | con1 c a iha =>
      intro x y z hzx hzy
      rw [subst]
      simp only [writes]
      rw [iha hzx hzy]
  | con2 c a b iha ihb =>
      intro x y z hzx hzy
      rw [subst]
      simp only [writes]
      rw [iha hzx hzy, ihb hzx hzy]
  | store s i v ihs ihv =>
      intro x y z hzx hzy
      rw [subst]
      simp only [writes]
      rw [isVarB_subst s hzx hzy, ihs hzx hzy, ihv hzx hzy]

/-- A substitution preserves construction: a node is substituted to a node, and no other
term shape is. -/
theorem built_subst (e : Expr) (x : Var) (v : Expr) :
    BuiltB e = true → BuiltB (subst x v e) = true := by
  induction e with
  | var z => intro h; simp [BuiltB] at h
  | lam w body ih => intro h; simp [BuiltB] at h
  | app f a ihf iha => intro h; simp [BuiltB] at h
  | bind w e₁ e₂ ih₁ ih₂ => intro h; simp [BuiltB] at h
  | matchC s c ys body ihs ihb => intro h; simp [BuiltB] at h
  | dup w ex ih => intro h; simp [BuiltB] at h
  | drop w ex ih => intro h; simp [BuiltB] at h
  | con0 c => intro _; simp [BuiltB, subst]
  | con1 c a iha => intro _; simp [BuiltB, subst]
  | con2 c a b iha ihb => intro _; simp [BuiltB, subst]
  | store s i v ihs ihv => intro h; simp [BuiltB] at h

/-! ## The typing survives the substitution

`subst_typed_var` is the substitution lemma the typing was missing: a typed term stays
typed when a fresh variable is substituted for a name the term does not rebind, read at
the environments whose occurrences the renaming moves. -/

/-- Substituting the variable `y` for `x` in a typed term keeps it typed, at the
environments that hold the renamed occurrences: `x`'s occurrences are the image's. The
restriction is what the same-environment statement lacks --- the substitute is a name the
term does not mention, the substituted name is not one the term rebinds, and neither name
is an occurrence the environments already hold under the other --- and
`ScidoniaTest/Typing`'s redex is the reason: a term that names `5` twice has no typing
whose write survives at the environments the step starts from. -/
theorem subst_typed_var (e : Expr) : ∀ {Δ Γ : Occs} {x y : Var}, Typed Δ Γ e →
    x ≠ y → y ∉ vars e → binds x e = false → y ∉ Δ → y ∉ Γ →
    Typed (Δ.map (rename x y)) (Γ.map (rename x y)) (subst x (.var y) e) := by
  induction e with
  | var z =>
      intro Δ Γ x y h hxy _ _ _ _
      cases h with
      | var hz =>
          by_cases hzx : z = x
          · rw [hzx] at hz ⊢
            rw [subst_var_self]
            exact Typed.var (Or.imp (fun h => List.mem_map.mpr ⟨x, h, rename_self x y⟩)
                                    (fun h => List.mem_map.mpr ⟨x, h, rename_self x y⟩) hz)
          · rw [subst_var_of_ne hzx]
            exact Typed.var (Or.imp (fun h => List.mem_map.mpr ⟨z, h, rename_of_ne hzx⟩)
                                    (fun h => List.mem_map.mpr ⟨z, h, rename_of_ne hzx⟩) hz)
  | lam w body ih =>
      intro Δ Γ x y h hxy hyfresh hhyg hyb hyg
      have hyw : y ≠ w := fun hh => hyfresh (List.mem_cons.mpr (Or.inl hh))
      have hyb' : y ∉ vars body := fun hh => hyfresh (List.mem_cons.mpr (Or.inr hh))
      have hybu : y ∉ uses body := fun hh => hyb' (mem_vars_of_mem_uses body hh)
      cases h with
      | lam hlin hbody =>
          have hwx : w ≠ x := by
            intro hh
            rw [hh] at hhyg
            simp [binds] at hhyg
          have hhyg' : binds x body = false := by
            rw [binds, ite_eq_right hwx] at hhyg
            exact hhyg
          have hyg' : y ∉ bindEnv Γ w (uses body) := by
            intro hh
            rcases (by simpa [bindEnv] using hh) with hh | ⟨hh, _, _⟩
            · exact hyw hh
            · exact hybu hh
          have hyb'' : y ∉ forget Δ w := by
            intro hh
            have hh' : y ∈ Δ ∧ y ≠ w := by simpa [forget] using hh
            exact hyb hh'.1
          rw [subst, ite_eq_right hwx]
          refine Typed.lam (x := w) ?_ ?_
          · intro hw
            rw [writes_subst_var body hwx (Ne.symm hyw)] at hw
            have h1 := hlin hw
            rw [uses_subst_var body (typed_pure hbody) hyb', count_map_rename_of_ne hwx (Ne.symm hyw)]
            exact h1
          · rw [uses_subst_var body (typed_pure hbody) hyb']
            rw [bindEnv_map (u := uses body) hwx (Ne.symm hyw) hybu hyg]
            rw [forget_map hwx (Ne.symm hyw)]
            exact ih hbody hxy hyb' hhyg' hyb'' hyg'
  | app f a ihf iha =>
      intro Δ Γ x y h hxy hyfresh hhyg hyb hyg
      have hyf : y ∉ vars f := fun hh => hyfresh (List.mem_append.mpr (Or.inl hh))
      have hya : y ∉ vars a := fun hh => hyfresh (List.mem_append.mpr (Or.inr hh))
      have hyfu : y ∉ uses f := fun hh => hyf (mem_vars_of_mem_uses f hh)
      have hyau : y ∉ uses a := fun hh => hya (mem_vars_of_mem_uses a hh)
      cases h with
      | app hf ha =>
          have hb : binds x f = false ∧ binds x a = false := by
            rw [binds] at hhyg
            exact Bool.or_eq_false_iff.mp hhyg
          refine Typed.app ?_ ?_
          · rw [uses_subst_var f (typed_pure hf) hyf]
            rw [claimEnv_map (u := uses f) hyfu hyg]
            exact ihf hf hxy hyf hb.1 hyb (not_mem_claimEnv hyg)
          · rw [uses_subst_var a (typed_pure ha) hya]
            rw [claimEnv_map (u := uses a) hyau hyg]
            exact iha ha hxy hya hb.2 hyb (not_mem_claimEnv hyg)
  | bind w e₁ e₂ ih₁ ih₂ =>
      intro Δ Γ x y h hxy hyfresh hhyg hyb hyg
      have hyw : y ≠ w := fun hh => hyfresh (List.mem_cons.mpr (Or.inl hh))
      have hy1 : y ∉ vars e₁ := fun hh =>
        hyfresh (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hh))))
      have hy2 : y ∉ vars e₂ := fun hh =>
        hyfresh (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr hh))))
      have hy1u : y ∉ uses e₁ := fun hh => hy1 (mem_vars_of_mem_uses e₁ hh)
      have hy2u : y ∉ uses e₂ := fun hh => hy2 (mem_vars_of_mem_uses e₂ hh)
      cases h with
      | bind hlin hbuild h₁ h₂ =>
          have hwx : w ≠ x := by
            intro hh
            rw [hh] at hhyg
            simp [binds] at hhyg
          have hhyg' : binds x e₁ = false ∧ binds x e₂ = false := by
            rw [binds, ite_eq_right hwx] at hhyg
            exact Bool.or_eq_false_iff.mp hhyg
          have hyg' : y ∉ bindEnv Γ w (uses e₂) := by
            intro hh
            rcases (by simpa [bindEnv] using hh) with hh | ⟨hh, _, _⟩
            · exact hyw hh
            · exact hy2u hh
          have hyb'' : y ∉ forget Δ w := by
            intro hh
            have hh' : y ∈ Δ ∧ y ≠ w := by simpa [forget] using hh
            exact hyb hh'.1
          rw [subst, ite_eq_right hwx]
          refine Typed.bind (x := w) ?_ ?_ ?_ ?_
          · intro hw
            rw [writes_subst_var e₂ hwx (Ne.symm hyw)] at hw
            have h1 := hlin hw
            rw [uses_subst_var e₂ (typed_pure h₂) hy2, count_map_rename_of_ne hwx (Ne.symm hyw)]
            exact h1
          · intro hw
            rw [writes_subst_var e₂ hwx (Ne.symm hyw)] at hw
            exact built_subst e₁ x (.var y) (hbuild hw)
          · rw [uses_subst_var e₁ (typed_pure h₁) hy1]
            rw [claimEnv_map (u := uses e₁) hy1u hyg]
            exact ih₁ h₁ hxy hy1 hhyg'.1 hyb (not_mem_claimEnv hyg)
          · rw [uses_subst_var e₂ (typed_pure h₂) hy2]
            rw [bindEnv_map (u := uses e₂) hwx (Ne.symm hyw) hy2u hyg]
            rw [forget_map hwx (Ne.symm hyw)]
            exact ih₂ h₂ hxy hy2 hhyg'.2 hyb'' hyg'
  | matchC s c ys body ihs ihb =>
      intro Δ Γ x y h hxy hyfresh hhyg hyb hyg
      have hys : y ∉ vars s := fun hh =>
        hyfresh (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hh))))
      have hyys : y ∉ ys := fun hh =>
        hyfresh (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hh))))
      have hybody : y ∉ vars body := fun hh => hyfresh (List.mem_append.mpr (Or.inr hh))
      have hysu : y ∉ uses s := fun hh => hys (mem_vars_of_mem_uses s hh)
      have hybodyu : y ∉ uses body := fun hh => hybody (mem_vars_of_mem_uses body hh)
      cases h with
      | matchC hlin hbuild hs hbody =>
          have hxys : x ∉ ys := by
            intro hh
            have hb := hhyg
            rw [binds, ite_eq_left hh] at hb
            simp at hb
          have hhyg' : binds x s = false ∧ binds x body = false := by
            rw [binds, ite_eq_right hxys, Bool.or_eq_false_iff] at hhyg
            exact hhyg
          have hyg' : y ∉ armEnv Γ ys (uses body) := by
            intro hh
            rcases (by simpa [armEnv] using hh) with hh | ⟨hh, _, _⟩
            · exact hyys hh
            · exact hybodyu hh
          rw [subst, ite_eq_right hxys]
          refine Typed.matchC (ys := ys) ?_ ?_ ?_ ?_
          · intro z hz hw
            have hzx : z ≠ x := fun hh => hxys (hh ▸ hz)
            have hzy : z ≠ y := fun hh => hyys (hh ▸ hz)
            rw [writes_subst_var body hzx hzy] at hw
            have h1 := hlin z hz hw
            rw [uses_subst_var body (typed_pure hbody) hybody, count_map_rename_of_ne hzx hzy]
            exact h1
          · intro z hz hw
            have hzx : z ≠ x := fun hh => hxys (hh ▸ hz)
            have hzy : z ≠ y := fun hh => hyys (hh ▸ hz)
            rw [writes_subst_var body hzx hzy] at hw
            exact built_subst s x (.var y) (hbuild z hz hw)
          · rw [uses_subst_var s (typed_pure hs) hys]
            rw [claimEnv_map (u := uses s) hysu hyg]
            exact ihs hs hxy hys hhyg'.1 hyb (not_mem_claimEnv hyg)
          · rw [uses_subst_var body (typed_pure hbody) hybody]
            rw [armEnv_map (u := uses body) hxys hyys hybodyu hyg]
            rw [forgetAll_map hxys hyys]
            refine ihb hbody hxy hybody hhyg'.2 ?_ hyg'
            intro hh
            have hh' : y ∈ Δ ∧ y ∉ ys := by simpa [forgetAll] using hh
            exact hyb hh'.1
  | dup w ex _ => intro Δ Γ x y h; cases h
  | drop w ex _ => intro Δ Γ x y h; cases h
  | con0 c =>
      intro Δ Γ x y h _ _ _ _ _
      cases h with
      | con0 => exact Typed.con0
  | con1 c a iha =>
      intro Δ Γ x y h hxy hyfresh hhyg hyb hyg
      have hyfreshu : y ∉ uses a := fun hh => hyfresh (mem_vars_of_mem_uses a hh)
      cases h with
      | con1 ha =>
          have hba : binds x a = false := by rw [binds] at hhyg; exact hhyg
          rw [subst]
          refine Typed.con1 ?_
          rw [uses_subst_var a (typed_pure ha) hyfresh]
          rw [claimEnv_map (u := uses a) hyfreshu hyg]
          exact iha ha hxy hyfresh hba hyb (not_mem_claimEnv hyg)
  | con2 c a b iha ihb =>
      intro Δ Γ x y h hxy hyfresh hhyg hyb hyg
      have hya : y ∉ vars a := fun hh => hyfresh (List.mem_append.mpr (Or.inl hh))
      have hyb2 : y ∉ vars b := fun hh => hyfresh (List.mem_append.mpr (Or.inr hh))
      have hyau : y ∉ uses a := fun hh => hya (mem_vars_of_mem_uses a hh)
      have hybu : y ∉ uses b := fun hh => hyb2 (mem_vars_of_mem_uses b hh)
      cases h with
      | con2 ha hb =>
          have hbinds : binds x a = false ∧ binds x b = false := by
            rw [binds] at hhyg
            exact Bool.or_eq_false_iff.mp hhyg
          rw [subst]
          refine Typed.con2 ?_ ?_
          · rw [uses_subst_var a (typed_pure ha) hya]
            rw [claimEnv_map (u := uses a) hyau hyg]
            exact iha ha hxy hya hbinds.1 hyb (not_mem_claimEnv hyg)
          · rw [uses_subst_var b (typed_pure hb) hyb2]
            rw [claimEnv_map (u := uses b) hybu hyg]
            exact ihb hb hxy hyb2 hbinds.2 hyb (not_mem_claimEnv hyg)
  | store s i v ihs ihv =>
      intro Δ Γ x y h hxy hyfresh hhyg hyb hyg
      obtain ⟨z, hz, hown, hborrow, hv⟩ :
          ∃ z, s = .var z ∧ Γ.count z = 1 ∧ z ∉ Δ ∧ Typed Δ (claimEnv Γ (uses v)) v := by
        cases h with
        | store hown hborrow hv => exact ⟨_, rfl, hown, hborrow, hv⟩
      subst hz
      have hyz : y ≠ z := by
        intro hh
        exact hyfresh (List.mem_append.mpr (Or.inl (by rw [hh]; simp [vars])))
      have hyv : y ∉ vars v := fun hh => hyfresh (List.mem_append.mpr (Or.inr hh))
      have hyvu : y ∉ uses v := fun hh => hyv (mem_vars_of_mem_uses v hh)
      have hhygv : binds x v = false := by
        rw [binds] at hhyg
        exact (Bool.or_eq_false_iff.mp hhyg).2
      by_cases hzx : z = x
      · rw [hzx] at hown hborrow
        rw [hzx]
        rw [subst, subst_var_self]
        refine Typed.store ?_ ?_ ?_
        · have hyΓ0 : Γ.count y = 0 := List.count_eq_zero.mpr hyg
          simp [count_map_rename_image hxy, hown, hyΓ0]
        · intro hmem
          obtain ⟨u, hu, hueq⟩ := List.mem_map.mp hmem
          rcases rename_eq_image hueq with hux | huy
          · exact hborrow (hux ▸ hu)
          · exact hyb (huy ▸ hu)
        · rw [uses_subst_var v (typed_pure hv) hyv]
          rw [claimEnv_map (u := uses v) hyvu hyg]
          exact ihv hv hxy hyv hhygv hyb (not_mem_claimEnv hyg)
      · rw [subst, subst_var_of_ne hzx]
        refine Typed.store ?_ ?_ ?_
        · rw [count_map_rename_of_ne hzx (Ne.symm hyz)]
          exact hown
        · intro hmem
          obtain ⟨u, hu, hueq⟩ := List.mem_map.mp hmem
          have huz : u = z := (rename_eq_iff hzx (Ne.symm hyz)).mp hueq
          rw [huz] at hu
          exact hborrow hu
        · rw [uses_subst_var v (typed_pure hv) hyv]
          rw [claimEnv_map (u := uses v) hyvu hyg]
          exact ihv hv hxy hyv hhygv hyb (not_mem_claimEnv hyg)

/-- The typing survives the source's own substitution step at the redex `(λx. body) (var
y)`: the body stays typed at the environments the renaming moves, when the substitute is
a name neither the body nor the environments already hold and the substituted name is not
one the body rebinds. The environments are the application rule's, read off the
abstraction: the body's borrowed occurrences with the binder forgotten, and the owned
occurrences the binder is bound beside. -/
theorem subst_typed_redex {Δ Γ : Occs} {x y : Var} {body : Expr}
    (h : Typed Δ Γ (.app (.lam x body) (.var y)))
    (hxy : x ≠ y) (hfresh : y ∉ vars body) (hhyg : binds x body = false)
    (hyb : y ∉ forget Δ x) :
    Typed ((forget Δ x).map (rename x y))
      ((bindEnv (claimEnv Γ (uses (.lam x body))) x (uses body)).map (rename x y))
      (subst x (.var y) body) := by
  cases h with
  | app hf _ =>
      cases hf with
      | lam hlin hl =>
          refine subst_typed_var body hl hxy hfresh hhyg hyb ?_
          intro hh
          rcases (by simpa [bindEnv] using hh) with hh | ⟨hh, _, _⟩
          · exact hxy hh.symm
          · exact hfresh (mem_vars_of_mem_uses body hh)

end Scidonia.RC
