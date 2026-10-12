/-
The syntax of the source calculus λPure and of the reference-counted target λRC
it is lowered into.

Reinking, Xie, de Moura and Leijen, *Perceus: Garbage Free Reference Counting
with Reuse* (PLDI 2021) writes a core calculus λ¹ and its reference-counted image
λRC. Figure 4 of that paper gives the syntax of both; this module carries one
inductive type for the two, because they differ only in that λRC may mention the
resource operations `dup` and `drop`. In the paper's terms this module has λRC as
the whole syntax and `Pure` as the fragment λPure — the source language — which
mentions neither operation. `dup` and `drop` are *not* source syntax: they are
written only by a lowering, which is why `Pure` excludes them and why the
lowering of `Scidonia.RC.Lower` has to synthesise them.

Three adaptations of the paper's Figure 4 are made, and each is stated where it
lands:

* Abstraction is a node of its own (`lam`). The paper's source rule that reduces
  an application is `(λx. e) v ⟶ e[x := v]`, so a term has to be able to write
  the abstraction.
* The pattern match scrutinises a *term* (`matchC`), as the paper's
  `case e { C x̄ → e′ }` writes it, and its one arm carries the constructor tag it
  answers to, the variables its binders are named by, and its body. The reduction
  of `Scidonia.RC.Pure` demands the subject be a node — the subject is a value
  position of the A-normal form — and the binders receive its fields. The subject
  is a term rather than a name because the reduction is a substitution semantics:
  a subject that is a name is resolved by the substitution of the binding that
  introduces it, which requires the syntax to hold a term there.
* `store` is this repository's write: slot `i` of the node the subject has is
  replaced by a value. It is the construct the whole claim lives in — whether
  that replacement lands in the node or in a copy of it is decided by the
  reference count of the node, which the target calculus and its semantics carry
  and this module does not.

**Why nodes are flat.** A node of Figure 4 is `C v̄`, a tag applied to a list of
subterms. This module writes nodes as a nullary form (`con0`), a unary form
(`con1`) and a binary form (`con2`) instead of carrying a list of subterms, so
that `Expr` is one simple inductive rather than a nested one. The reason is a
property of this toolchain, measured on this very type: `induction` refuses a
nested inductive type ("The `induction` tactic does not support the type …
because it is a nested inductive type"), `deriving DecidableEq` does not apply
to one, a recursion over a list of subterms is rejected by the structural
checker when written with `List.all` and then does not reduce, and a nested shape
forces a hand-rolled boolean equality to stand in for the one the deriving
handler would have written. Every derivation-level proof in the later modules
inducts, so the flat shape is what makes the development possible at all, and the
cost is that a node has at most two slots outside the nullary form.

## What is defined

* `Expr`, the syntax: variables, abstraction, application, binding, match, the
  resource operations, a nullary/unary/binary node construction and the write.
* `Pure`, the source fragment: no `dup` and no `drop` anywhere.
* `pureB` and `pureB_iff`, the decidable test of membership in the fragment
  agree with `Pure`, so `decide (Pure e)` is a statement about `Pure e`.
* the purity of a node read off its subterms (`pure_lam_iff`, `pure_app_iff`,
  `pure_bind_iff`, `pure_matchC_iff`, `pure_con0`, `pure_con1_iff`,
  `pure_con2_iff`, `pure_store_iff`), which is how the later modules decompose a
  term, and the two forms that are never pure (`not_pure_dup`, `not_pure_drop`).
* `uses`, the free occurrences of a variable as a list read for its
  multiplicities, and `Closed`, the terms in which no variable occurs free, which
  `decide` settles at a concrete term because `uses` is a boolean recursion.

## What is modelled, and what is not

Constructors are tags (`Ctor`), and a node's slots are their fields; nothing here
says what a tag is, and no arity is enforced, so a tag may be written at more
than one of the three forms in one term. A variable is a natural number, and
binders are not required to be distinct: a later binder of a name shadows an
earlier one, as the substitution of `Scidonia.RC.Pure` reads it, and as the free
occurrences `uses` counts read it here. An arm's binders are a list of names
rather than a list of subterms, which is what keeps the match flat.

Nothing here is a theorem about a program: the module fixes a language, its
source fragment, its free variables and its closed terms, and the decidable test
the later modules and the checks read it back with.
-/

namespace Scidonia.RC

/-- A variable name. Variables are natural numbers; a binder of a name shadows an
earlier binder of the same name. -/
abbrev Var := Nat

/-- A constructor tag. A node's arity is not part of the tag: the three node
forms below fix the arities the syntax can write, and nothing checks that a tag
is written at one of them throughout a term. -/
abbrev Ctor := Nat

/-- The syntax of λRC: λ¹'s terms extended with the resource operations `dup` and
`drop`.

| node | the paper's form | reading |
|---|---|---|
| `var x` | `x` | the variable `x` |
| `lam x body` | `λx. body` | the abstraction binding `x` in `body` |
| `app f a` | `f a` | application |
| `bind x e₁ e₂` | `val x = e₁; e₂` | evaluate `e₁`, bind it to `x`, then run `e₂` |
| `matchC s c ys body` | `case s { C ȳ → e }` | scrutinise `s` against the arm for the tag `c` |
| `dup x e` | `dup x; e` | a further owned occurrence of `x`, then `e` |
| `drop x e` | `drop x; e` | release the owned occurrence of `x`, then `e` |
| `con0 c` | `C` | the nullary node `c` |
| `con1 c a` | `C a` | the unary node `c` with field `a` |
| `con2 c a b` | `C a b` | the binary node `c` with fields `a` and `b` |
| `store s i v` | — | slot `i` of the node `s` is set to `v` |

An arm binds the variables of `ys` to the fields of the matched node, in order.
The match takes the arm whose tag is the node's; there is one arm, which is what
λ¹'s mutually exclusive patterns make sufficient. -/
inductive Expr where
  /-- The variable `x`. -/
  | var (x : Var)
  /-- The abstraction `λx. body`, binding `x` in `body`. -/
  | lam (x : Var) (body : Expr)
  /-- The application `f a`. -/
  | app (f a : Expr)
  /-- The binding `val x = e₁; e₂`: evaluate `e₁`, bind it to `x`, then run `e₂`. -/
  | bind (x : Var) (e₁ e₂ : Expr)
  /-- The match `match s { c ȳ → body }`, scrutinising the term `s` against the
  arm for the tag `c` and binding the matched node's fields to `ys`. -/
  | matchC (s : Expr) (c : Ctor) (ys : List Var) (body : Expr)
  /-- `dup x; e`: a further owned occurrence of `x`, then `e`. Written only by a
  lowering: the source fragment `Pure` excludes it. -/
  | dup (x : Var) (e : Expr)
  /-- `drop x; e`: the owned occurrence of `x` is released, then `e`. Written
  only by a lowering: the source fragment `Pure` excludes it. -/
  | drop (x : Var) (e : Expr)
  /-- The nullary node `c`. -/
  | con0 (c : Ctor)
  /-- The unary node `c` with field `a`. -/
  | con1 (c : Ctor) (a : Expr)
  /-- The binary node `c` with fields `a` and `b`. -/
  | con2 (c : Ctor) (a b : Expr)
  /-- The write: slot `i` of the node `s` is set to `v`. -/
  | store (s : Expr) (i : Nat) (v : Expr)
  deriving DecidableEq, Repr

/-- The source fragment λPure: the terms that mention no `dup` and no `drop`
anywhere. -/
inductive Pure : Expr → Prop where
  /-- A variable is pure. -/
  | var (x : Var) : Pure (.var x)
  /-- An abstraction is pure exactly when its body is. -/
  | lam {x : Var} {body : Expr} (h : Pure body) : Pure (.lam x body)
  /-- An application is pure exactly when its two subterms are. -/
  | app {f a : Expr} (hf : Pure f) (ha : Pure a) : Pure (.app f a)
  /-- A binding is pure exactly when its two subterms are. -/
  | bind {x : Var} {e₁ e₂ : Expr} (h₁ : Pure e₁) (h₂ : Pure e₂) : Pure (.bind x e₁ e₂)
  /-- A match is pure exactly when its subject and its arm's body are. -/
  | matchC {s : Expr} {c : Ctor} {ys : List Var} {body : Expr} (hs : Pure s)
      (h : Pure body) : Pure (.matchC s c ys body)
  /-- A nullary node is pure. -/
  | con0 (c : Ctor) : Pure (.con0 c)
  /-- A unary node is pure exactly when its field is. -/
  | con1 {c : Ctor} {a : Expr} (h : Pure a) : Pure (.con1 c a)
  /-- A binary node is pure exactly when its two fields are. -/
  | con2 {c : Ctor} {a b : Expr} (h₁ : Pure a) (h₂ : Pure b) : Pure (.con2 c a b)
  /-- A write is pure exactly when its subject and its value are. -/
  | store {s : Expr} {i : Nat} {v : Expr} (hs : Pure s) (h : Pure v) : Pure (.store s i v)

/-- Whether a term is a term of the source fragment: no `dup` and no `drop`
anywhere. The recursion is structural on the term, so the kernel reduces it at a
concrete term and a `#guard` can evaluate it. -/
def pureB : Expr → Bool
  | .var _ => true
  | .lam _ body => pureB body
  | .app f a => pureB f && pureB a
  | .bind _ e₁ e₂ => pureB e₁ && pureB e₂
  | .matchC s _ _ body => pureB s && pureB body
  | .dup _ _ => false
  | .drop _ _ => false
  | .con0 _ => true
  | .con1 _ a => pureB a
  | .con2 _ a b => pureB a && pureB b
  | .store s _ v => pureB s && pureB v

/-- The decidable test of purity agrees with `Pure`, so a term's purity is
decided by evaluating `pureB` at it. -/
theorem pureB_iff : ∀ (e : Expr), pureB e = true ↔ Pure e
  | .var x => Iff.intro (fun _ => Pure.var x) (fun _ => rfl)
  | .lam x body =>
      Iff.intro (fun h => Pure.lam ((pureB_iff body).mp h))
        (fun h => by cases h with | lam h => exact (pureB_iff body).mpr h)
  | .app f a =>
      Iff.intro
        (fun h => by
          rw [pureB, Bool.and_eq_true] at h
          exact Pure.app ((pureB_iff f).mp h.1) ((pureB_iff a).mp h.2))
        (fun h => by
          cases h with
          | app hf ha => rw [pureB, Bool.and_eq_true]; exact ⟨(pureB_iff f).mpr hf, (pureB_iff a).mpr ha⟩)
  | .bind x e₁ e₂ =>
      Iff.intro
        (fun h => by
          rw [pureB, Bool.and_eq_true] at h
          exact Pure.bind ((pureB_iff e₁).mp h.1) ((pureB_iff e₂).mp h.2))
        (fun h => by
          cases h with
          | bind h₁ h₂ => rw [pureB, Bool.and_eq_true]; exact ⟨(pureB_iff e₁).mpr h₁, (pureB_iff e₂).mpr h₂⟩)
  | .matchC s c ys body =>
      Iff.intro
        (fun h => by
          rw [pureB, Bool.and_eq_true] at h
          exact Pure.matchC ((pureB_iff s).mp h.1) ((pureB_iff body).mp h.2))
        (fun h => by
          cases h with
          | matchC hs h => rw [pureB, Bool.and_eq_true]; exact ⟨(pureB_iff s).mpr hs, (pureB_iff body).mpr h⟩)
  | .dup x e => Iff.intro (fun h => by simp [pureB] at h) (fun h => by cases h)
  | .drop x e => Iff.intro (fun h => by simp [pureB] at h) (fun h => by cases h)
  | .con0 c => Iff.intro (fun _ => Pure.con0 c) (fun _ => rfl)
  | .con1 c a =>
      Iff.intro (fun h => Pure.con1 ((pureB_iff a).mp h))
        (fun h => by cases h with | con1 h => exact (pureB_iff a).mpr h)
  | .con2 c a b =>
      Iff.intro
        (fun h => by
          rw [pureB, Bool.and_eq_true] at h
          exact Pure.con2 ((pureB_iff a).mp h.1) ((pureB_iff b).mp h.2))
        (fun h => by
          cases h with
          | con2 h₁ h₂ => rw [pureB, Bool.and_eq_true]; exact ⟨(pureB_iff a).mpr h₁, (pureB_iff b).mpr h₂⟩)
  | .store s i v =>
      Iff.intro
        (fun h => by
          rw [pureB, Bool.and_eq_true] at h
          exact Pure.store ((pureB_iff s).mp h.1) ((pureB_iff v).mp h.2))
        (fun h => by
          cases h with
          | store hs h => rw [pureB, Bool.and_eq_true]; exact ⟨(pureB_iff s).mpr hs, (pureB_iff v).mpr h⟩)

/-- Purity is decidable at a concrete term, because `pureB` is a boolean
recursion. -/
instance (e : Expr) : Decidable (Pure e) :=
  if h : pureB e = true then isTrue ((pureB_iff e).mp h)
  else isFalse (fun hp => h ((pureB_iff e).mpr hp))

/-- An abstraction is pure exactly when its body is. -/
theorem pure_lam_iff (x : Var) (body : Expr) : Pure (.lam x body) ↔ Pure body :=
  Iff.intro (fun h => by cases h with | lam h => exact h) (fun h => Pure.lam h)

/-- An application is pure exactly when its two subterms are. -/
theorem pure_app_iff (f a : Expr) : Pure (.app f a) ↔ Pure f ∧ Pure a :=
  Iff.intro (fun h => by cases h with | app hf ha => exact ⟨hf, ha⟩) (fun h => Pure.app h.1 h.2)

/-- A binding is pure exactly when its two subterms are. -/
theorem pure_bind_iff (x : Var) (e₁ e₂ : Expr) :
    Pure (.bind x e₁ e₂) ↔ Pure e₁ ∧ Pure e₂ :=
  Iff.intro (fun h => by cases h with | bind h₁ h₂ => exact ⟨h₁, h₂⟩)
    (fun h => Pure.bind h.1 h.2)

/-- A match is pure exactly when its subject and its arm's body are: its binders
are names, and a name is not a term. -/
theorem pure_matchC_iff (s : Expr) (c : Ctor) (ys : List Var) (body : Expr) :
    Pure (.matchC s c ys body) ↔ Pure s ∧ Pure body :=
  Iff.intro (fun h => by cases h with | matchC hs h => exact ⟨hs, h⟩)
    (fun h => Pure.matchC h.1 h.2)

/-- A unary node is pure exactly when its field is. -/
theorem pure_con1_iff (c : Ctor) (a : Expr) : Pure (.con1 c a) ↔ Pure a :=
  Iff.intro (fun h => by cases h with | con1 h => exact h) (fun h => Pure.con1 h)

/-- A binary node is pure exactly when its two fields are. -/
theorem pure_con2_iff (c : Ctor) (a b : Expr) : Pure (.con2 c a b) ↔ Pure a ∧ Pure b :=
  Iff.intro (fun h => by cases h with | con2 h₁ h₂ => exact ⟨h₁, h₂⟩)
    (fun h => Pure.con2 h.1 h.2)

/-- A write is pure exactly when its subject and its value are: its slot index is
a number, and a number is not a term. -/
theorem pure_store_iff (s : Expr) (i : Nat) (v : Expr) : Pure (.store s i v) ↔ Pure s ∧ Pure v :=
  Iff.intro (fun h => by cases h with | store hs h => exact ⟨hs, h⟩)
    (fun h => Pure.store h.1 h.2)

/-- A nullary node is pure. -/
theorem pure_con0 (c : Ctor) : Pure (.con0 c) := Pure.con0 c

/-- A `dup` node is never pure. -/
theorem not_pure_dup (x : Var) (e : Expr) : ¬ Pure (.dup x e) := by
  intro h
  cases h

/-- A `drop` node is never pure. -/
theorem not_pure_drop (x : Var) (e : Expr) : ¬ Pure (.drop x e) := by
  intro h
  cases h

/-! ## Free variables

The free occurrences of a variable, as a multiset in list form, and the closed
terms: the account the substitution of `Scidonia.RC.Pure` is read against, and
the occurrences the environments of `Scidonia.RC.Lower` are computed from. -/

/-- The free occurrences of a variable, as a multiset in list form. A binder's
name is removed from the whole of its scope, so an inner binder of the same name
shadows an outer one for the free occurrences as well. A match's subject and its
arm's binders are occurrences of the term like any other — the subject outside
the binders' scope and the body under them; a `dup` or a `drop` node holds an
occurrence of its name besides the occurrences of its body, and neither is source
syntax, so the recursion is total on the syntax only because it has to be. -/
def uses : Expr → List Var
  | .var x => [x]
  | .lam x body => (uses body).filter (fun y => y ≠ x)
  | .app f a => uses f ++ uses a
  | .bind x e₁ e₂ => uses e₁ ++ (uses e₂).filter (fun y => y ≠ x)
  | .matchC s _ ys body => uses s ++ (uses body).filter (fun y => y ∉ ys)
  | .dup x e => x :: uses e
  | .drop x e => x :: uses e
  | .con0 _ => []
  | .con1 _ a => uses a
  | .con2 _ a b => uses a ++ uses b
  | .store s _ v => uses s ++ uses v

/-- A term is closed when no variable occurs free in it: `uses` is empty. This is
the discipline the reduction of `Scidonia.RC.Pure` is stated for, and the
hypothesis under which its substitution inserts no free variable under a binder —
a closed term has no free variable for a binder to capture. -/
def Closed (e : Expr) : Prop := uses e = []

/-- Closedness is decidable at a concrete term: `uses` is a boolean recursion and
its value is compared with the empty list, so `decide` settles `Closed e` there
and a `#guard` can evaluate it. -/
instance (e : Expr) : Decidable (Closed e) :=
  inferInstanceAs (Decidable (uses e = []))

end Scidonia.RC
