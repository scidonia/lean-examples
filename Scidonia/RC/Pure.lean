/-
The source semantics: a strict, deterministic small-step reduction of the
calculus of `Scidonia.RC.Syntax`, and the purity preservation that makes the
source fragment worth naming.

Reinking, Xie, de Moura and Leijen, *Perceus: Garbage Free Reference Counting
with Reuse* (PLDI 2021), Figure 6 gives the source calculus's reduction as
`E[e] ⟶ E[e']` over redexes

* `(λx. e) v ⟶ e[x := v]`,
* `val x = v; e ⟶ e[x := v]`,
* `match x { C ȳ → e } ⟶ e[ȳ := v̄]` where `x` names a node, and
* the write: the node `x` names has slot `i` set to the value `v`,

with `E` ranging over the evaluation contexts `□`, `E e`, `v E` and
`val x = E; e`. This module writes those redexes as the judgement `Root`, the
same rules plus one congruence rule per context former as the judgement `Step`,
and proves `step_iff_ectx`: a step is exactly a redex inside a well-formed
evaluation context (`Ectx.plug`). The congruence rules are the paper's
`E[e] ⟶ E[e']` written rule by rule, so the two judgements are two views of one
relation rather than two semantics.

**The environment.** A configuration is a term under an *environment* — the value
each variable names — rather than under a substitution. The paper's rules are
substitution rules and this module's are their environment form: a binder extends
the environment instead of rewriting the body, and a use of a variable the
environment does not bind is *stuck* rather than unbound. The syntax forces the
choice: the match and the write name a *variable*, so a substitution would have
to rewrite a match's scrutinee from a variable into the node that variable names,
which no substitution can do. A variable is a value (the paper's `v ::= x | C v̄`,
and `Value` includes it), so the beta rule has a second form that resolves the
function position through the environment (`Root.betaVar`) beside the paper's own
form (`Root.beta`).

**A-normal form.** λ¹ is an A-normal-form calculus: the argument of an
application and the value of a write are *values*, and the computation that
produces them is sequenced by `val` bindings. This module reads the syntax that
way, which is what makes its reduction the paper's: an application whose argument
is not a value, and a write whose value is not a value, are *stuck* rather than
reducible, because the paper's rules have only value positions in those places
and its contexts do not descend into them. `Step` therefore has a congruence rule
for the function position of an application, for the argument position of an
application whose function is a value, and for the bound term of a binding, and
none for the fields of a node or the binders of a match. A source term that is
not in that shape is a term this module has no step for, and the lowering of
`Scidonia.RC.Lower` is what puts a term into it.

**The write.** At the source the write is *functional*: `store x i v` reduces to
the node `x` names with slot `i` replaced by `v`, a value. Nothing here is
destructive and nothing here has a reference count; whether the target's write
updates in place is a property of the target calculus and its count, which this
slice does not build. What the source fixes is the shape of the result.

## What is proved

* `valueB_iff`: the decidable test of valuehood agrees with `Value`; the shapes
  that are never values are separated out (`not_value_app` and the rest), and
  `value_canonical` says every value is a variable, an abstraction or a node.
* `value_no_step`: no value steps — the observation every overlap in the
  determinism proof is separated by, and there are no others.
* `root_deterministic` and `step_deterministic`: a configuration has at most one
  step, and the environment and the contractum are both unique.
* `step_iff_ectx`: a step is a redex inside a well-formed evaluation context, and
  conversely, which is the paper's `E[e] ⟶ E[e']` for this syntax.
* `rootStep?_sound` and `step?_sound`: the evaluator the checks guard on computes
  only steps of `Step`. It is written structurally on the term, so a `#guard` can
  evaluate it.
* `StepStar` and `pure_steps_pure`: along any evaluation path a term of the
  source fragment stays in the fragment and so does the environment — no `dup`
  and no `drop` ever appears. That is the erasure sanity fact the fragment is for
  and what the lowering is read against.

## What is modelled, and what is trusted

The environment is a list of bindings read from the front, so a later binding of
a name shadows an earlier one — the shadowing `Scidonia.RC.Syntax` leaves in the
syntax. The environment is not restricted to values: a rule that would bind a
non-value never applies, because every rule that extends the environment demands
a value. Purity is carried as a hypothesis on the environment (`PureEnv`, its
bindings are pure values) rather than read off the syntax, because the syntax says
nothing about what an environment holds.

A node's fields are read with `nodeFields`: none for a nullary node, one for a
unary node and two for a binary one, and an arm binds the variables it names to
the fields in order, which the match rule admits only when the two lists are the
same length. A write's slot index is a natural number and `slotUpdate` answers
`none` outside a node's slots, so a write at a slot a node does not have is
stuck; the node and the written value are required to be values, so a write's
contractum is a value (`slotUpdate_value`).

Nothing here is a theorem about a compiled program, a reference count, or the
target calculus: the reduction is the source calculus's own, it mentions no
resource operation, and its role in this development is to be the semantics a
lowering is defined against.
-/

import Scidonia.RC.Syntax

namespace Scidonia.RC

/-! ## Values

λ¹'s `v ::= x | C v̄`, and the abstraction the source calculus carries. -/

/-- A value: a variable, an abstraction, or a node applied to values. -/
inductive Value : Expr → Prop where
  /-- A variable is a value. -/
  | var (x : Var) : Value (.var x)
  /-- An abstraction is a value. -/
  | lam (x : Var) (body : Expr) : Value (.lam x body)
  /-- A nullary node is a value. -/
  | con0 (c : Ctor) : Value (.con0 c)
  /-- A unary node whose field is a value is a value. -/
  | con1 {c : Ctor} {a : Expr} (h : Value a) : Value (.con1 c a)
  /-- A binary node whose two fields are values is a value. -/
  | con2 {c : Ctor} {a b : Expr} (h₁ : Value a) (h₂ : Value b) : Value (.con2 c a b)

/-- A unary node is a value exactly when its field is. -/
theorem value_con1_iff (c : Ctor) (a : Expr) : Value (.con1 c a) ↔ Value a :=
  Iff.intro (fun h => by cases h with | con1 h => exact h) (fun h => Value.con1 h)

/-- A binary node is a value exactly when its two fields are. -/
theorem value_con2_iff (c : Ctor) (a b : Expr) : Value (.con2 c a b) ↔ Value a ∧ Value b :=
  Iff.intro (fun h => by cases h with | con2 h₁ h₂ => exact ⟨h₁, h₂⟩)
    (fun h => Value.con2 h.1 h.2)

/-- Every value is a variable, an abstraction or a node: the shapes `Value` admits
are the only ones a value has. -/
theorem value_canonical {e : Expr} (h : Value e) :
    (∃ x, e = .var x) ∨ (∃ x body, e = .lam x body) ∨ (∃ c, e = .con0 c)
      ∨ (∃ c a, e = .con1 c a) ∨ (∃ c a b, e = .con2 c a b) := by
  cases h with
  | var x => exact Or.inl ⟨x, rfl⟩
  | lam x body => exact Or.inr (Or.inl ⟨x, body, rfl⟩)
  | con0 c => exact Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))
  | con1 h => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
  | con2 h₁ h₂ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl⟩)))

/-- An application is not a value. -/
@[simp] theorem not_value_app (f a : Expr) : ¬ Value (.app f a) := by
  intro h
  cases h

/-- A binding is not a value. -/
@[simp] theorem not_value_bind (x : Var) (e₁ e₂ : Expr) : ¬ Value (.bind x e₁ e₂) := by
  intro h
  cases h

/-- A match is not a value. -/
@[simp] theorem not_value_matchC (x : Var) (c : Ctor) (ys : List Var) (body : Expr) :
    ¬ Value (.matchC x c ys body) := by
  intro h
  cases h

/-- A `dup` node is not a value. -/
@[simp] theorem not_value_dup (x : Var) (e : Expr) : ¬ Value (.dup x e) := by
  intro h
  cases h

/-- A `drop` node is not a value. -/
@[simp] theorem not_value_drop (x : Var) (e : Expr) : ¬ Value (.drop x e) := by
  intro h
  cases h

/-- A write is not a value. -/
@[simp] theorem not_value_store (x : Var) (i : Nat) (v : Expr) : ¬ Value (.store x i v) := by
  intro h
  cases h

/-- The decidable test of valuehood. Its recursion is structural on the term, so
the kernel reduces the test at a concrete term and a `#guard` can evaluate it. -/
def valueB : Expr → Bool
  | .var _ => true
  | .lam _ _ => true
  | .app _ _ => false
  | .bind _ _ _ => false
  | .matchC _ _ _ _ => false
  | .dup _ _ => false
  | .drop _ _ => false
  | .con0 _ => true
  | .con1 _ a => valueB a
  | .con2 _ a b => valueB a && valueB b
  | .store _ _ _ => false

/-- The decidable test of valuehood agrees with `Value`. -/
theorem valueB_iff : ∀ (e : Expr), valueB e = true ↔ Value e
  | .var x => Iff.intro (fun _ => Value.var x) (fun _ => rfl)
  | .lam x body => Iff.intro (fun _ => Value.lam x body) (fun _ => rfl)
  | .app f a =>
      Iff.intro (fun h => absurd h (by simp [valueB])) (fun h => absurd h (not_value_app f a))
  | .bind x e₁ e₂ =>
      Iff.intro (fun h => absurd h (by simp [valueB]))
        (fun h => absurd h (not_value_bind x e₁ e₂))
  | .matchC x c ys body =>
      Iff.intro (fun h => absurd h (by simp [valueB]))
        (fun h => absurd h (not_value_matchC x c ys body))
  | .dup x e =>
      Iff.intro (fun h => absurd h (by simp [valueB])) (fun h => absurd h (not_value_dup x e))
  | .drop x e =>
      Iff.intro (fun h => absurd h (by simp [valueB])) (fun h => absurd h (not_value_drop x e))
  | .con0 c => Iff.intro (fun _ => Value.con0 c) (fun _ => rfl)
  | .con1 c a =>
      Iff.intro (fun h => Value.con1 ((valueB_iff a).mp h))
        (fun h => (valueB_iff a).mpr ((value_con1_iff c a).mp h))
  | .con2 c a b =>
      Iff.intro
        (fun h => by
          rw [valueB, Bool.and_eq_true] at h
          exact Value.con2 ((valueB_iff a).mp h.1) ((valueB_iff b).mp h.2))
        (fun h => by
          rw [valueB, Bool.and_eq_true]
          exact ⟨(valueB_iff a).mpr ((value_con2_iff c a b).mp h).1,
            (valueB_iff b).mpr ((value_con2_iff c a b).mp h).2⟩)
  | .store x i v =>
      Iff.intro (fun h => absurd h (by simp [valueB])) (fun h => absurd h (not_value_store x i v))

/-- Valuehood is decidable at a concrete term. -/
instance (e : Expr) : Decidable (Value e) :=
  if h : valueB e = true then isTrue ((valueB_iff e).mp h)
  else isFalse (fun hv => h ((valueB_iff e).mpr hv))

/-! ## Nodes

The tag a term is written at, its fields, and the write's slot update. -/

/-- The tag of a node, or `none` for a term that is not a node. -/
def nodeTag? : Expr → Option Ctor
  | .var _ => none
  | .lam _ _ => none
  | .app _ _ => none
  | .bind _ _ _ => none
  | .matchC _ _ _ _ => none
  | .dup _ _ => none
  | .drop _ _ => none
  | .con0 c => some c
  | .con1 c _ => some c
  | .con2 c _ _ => some c
  | .store _ _ _ => none

/-- A node's fields, in order; the empty list for a term that is not a node. -/
def nodeFields : Expr → List Expr
  | .var _ => []
  | .lam _ _ => []
  | .app _ _ => []
  | .bind _ _ _ => []
  | .matchC _ _ _ _ => []
  | .dup _ _ => []
  | .drop _ _ => []
  | .con0 _ => []
  | .con1 _ a => [a]
  | .con2 _ a b => [a, b]
  | .store _ _ _ => []

/-- The node `n` with slot `i` replaced by `v`, or `none` when `n` has no slot
`i`: a nullary node has none, a unary node has slot `0` and a binary node has
slots `0` and `1`. -/
def slotUpdate : Expr → Nat → Expr → Option Expr
  | .var _, _, _ => none
  | .lam _ _, _, _ => none
  | .app _ _, _, _ => none
  | .bind _ _ _, _, _ => none
  | .matchC _ _ _ _, _, _ => none
  | .dup _ _, _, _ => none
  | .drop _ _, _, _ => none
  | .con0 _, _, _ => none
  | .con1 c _, i, v => if i = 0 then some (.con1 c v) else none
  | .con2 c a b, i, v =>
      if i = 0 then some (.con2 c v b) else if i = 1 then some (.con2 c a v) else none
  | .store _ _ _, _, _ => none

/-- A member of a node's fields is pure when the node is. -/
theorem nodeFields_pure {n : Expr} (hn : Pure n) : ∀ a ∈ nodeFields n, Pure a := by
  cases n with
  | con0 c => intro a ha; simp [nodeFields] at ha
  | con1 c a =>
      have hfield := (pure_con1_iff c a).mp hn
      intro b hb
      simp only [nodeFields, List.mem_singleton] at hb
      rw [hb]
      exact hfield
  | con2 c a b =>
      have hfields := (pure_con2_iff c a b).mp hn
      intro k hk
      simp only [nodeFields, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact hfields.1
      · exact hfields.2
  | var x => intro a ha; simp [nodeFields] at ha
  | lam x body => intro a ha; simp [nodeFields] at ha
  | app f a => intro k hk; simp [nodeFields] at hk
  | bind x e₁ e₂ => intro k hk; simp [nodeFields] at hk
  | matchC x c ys body => intro k hk; simp [nodeFields] at hk
  | dup x e => intro k hk; simp [nodeFields] at hk
  | drop x e => intro k hk; simp [nodeFields] at hk
  | store x i v => intro k hk; simp [nodeFields] at hk

/-- A write of a pure value into a pure node is pure: the node keeps its fields
and the written value takes the written slot. -/
theorem slotUpdate_pure {n n' : Expr} {i : Nat} {v : Expr} (hn : Pure n) (hv : Pure v) :
    slotUpdate n i v = some n' → Pure n' := by
  intro h
  cases n with
  | con1 c a =>
      simp only [slotUpdate] at h
      split at h
      · rw [← Option.some.inj h]
        exact Pure.con1 hv
      · simp at h
  | con2 c a b =>
      have hfields := (pure_con2_iff c a b).mp hn
      simp only [slotUpdate] at h
      split at h
      · rw [← Option.some.inj h]
        exact Pure.con2 hv hfields.2
      · split at h
        · rw [← Option.some.inj h]
          exact Pure.con2 hfields.1 hv
        · simp at h
  | var x => simp [slotUpdate] at h
  | lam x body => simp [slotUpdate] at h
  | app f a => simp [slotUpdate] at h
  | bind x e₁ e₂ => simp [slotUpdate] at h
  | matchC x c ys body => simp [slotUpdate] at h
  | dup x e => simp [slotUpdate] at h
  | drop x e => simp [slotUpdate] at h
  | con0 c => simp [slotUpdate] at h
  | store x i' v' => simp [slotUpdate] at h

/-- A write of a value into a value is a value. -/
theorem slotUpdate_value {n n' : Expr} {i : Nat} {v : Expr} (hn : Value n) (hv : Value v) :
    slotUpdate n i v = some n' → Value n' := by
  intro h
  cases n with
  | con0 c => simp [slotUpdate] at h
  | con1 c a =>
      simp only [slotUpdate] at h
      split at h
      · rw [← Option.some.inj h]
        exact Value.con1 hv
      · simp at h
  | con2 c a b =>
      have hfields := (value_con2_iff c a b).mp hn
      simp only [slotUpdate] at h
      split at h
      · rw [← Option.some.inj h]
        exact Value.con2 hv hfields.2
      · split at h
        · rw [← Option.some.inj h]
          exact Value.con2 hfields.1 hv
        · simp at h
  | var x => simp [slotUpdate] at h
  | lam x body => simp [slotUpdate] at h
  | app f a => simp [slotUpdate] at h
  | bind x e₁ e₂ => simp [slotUpdate] at h
  | matchC x c ys body => simp [slotUpdate] at h
  | dup x e => simp [slotUpdate] at h
  | drop x e => simp [slotUpdate] at h
  | store x i' v' => simp [slotUpdate] at h

/-! ## Environments

The bindings a term is reduced under: the value each variable names, most recent
binding first. The environment is the paper's substitution in binding form, which
is what the match and the write need, since both name a variable. -/

/-- An environment: the bindings in force, most recent first. -/
abbrev Env := List (Var × Expr)

/-- The value the environment binds a variable to, or `none` when it binds none;
the first binding of a name wins. -/
def Env.get? : Env → Var → Option Expr
  | [], _ => none
  | (y, v) :: t, x => if y = x then some v else Env.get? t x

/-- The environment with one further binding, which shadows any earlier binding
of the same name. -/
def Env.extend (ρ : Env) (x : Var) (v : Expr) : Env := (x, v) :: ρ

/-- The environment with one binding per variable of `xs`, taken from `vs` in
order, the first variable of `xs` keeping the first value of `vs` against the
shadowing of the later ones. When the lists differ in length the shorter ends the
walk, so an arm whose binder list is shorter than the matched node's fields binds
the fields it has and leaves the rest unbound. -/
def Env.extendAll (ρ : Env) : List Var → List Expr → Env
  | [], _ => ρ
  | _ :: _, [] => ρ
  | x :: xs, v :: vs => Env.extendAll (Env.extend ρ x v) xs vs

/-- The most recent binding of a variable is the one the extended environment
gives it. -/
@[simp] theorem Env.get?_extend_self (ρ : Env) (x : Var) (v : Expr) :
    Env.get? (Env.extend ρ x v) x = some v := by
  simp [Env.extend, Env.get?]

/-- A binding of another name is left to the environment behind it. -/
theorem Env.get?_extend_of_ne (ρ : Env) {x y : Var} (h : x ≠ y) (v : Expr) :
    Env.get? (Env.extend ρ x v) y = Env.get? ρ y := by
  simp [Env.extend, Env.get?, h]

/-- Two lookups of one variable in one environment agree: the environment is a
function of the variable, so two derivations that read it read the same value.
This is what separates two derivations that both resolve a variable without that
variable appearing in the term they step. -/
theorem env_get?_eq {ρ : Env} {x : Var} {v w : Expr} (h : Env.get? ρ x = some v)
    (h' : Env.get? ρ x = some w) : v = w := by
  rw [h] at h'
  exact Option.some.inj h'

/-- Every value an environment binds is pure. This is the hypothesis the purity
statement carries: the syntax says nothing about what an environment holds, and
the environment does not grow impure by itself. -/
def PureEnv (ρ : Env) : Prop := ∀ x v, Env.get? ρ x = some v → Pure v

/-- The environment that binds nothing is pure, because it binds no value. -/
theorem pureEnv_nil : PureEnv ([] : Env) := by
  intro x v hx
  simp [Env.get?] at hx

/-- A binding of a pure value keeps the environment pure. -/
theorem PureEnv.extend {ρ : Env} {x : Var} {v : Expr} (h : PureEnv ρ) (hv : Pure v) :
    PureEnv (Env.extend ρ x v) := by
  intro y w hw
  by_cases hyx : y = x
  · subst hyx
    rw [Env.get?_extend_self] at hw
    cases hw
    exact hv
  · rw [Env.get?_extend_of_ne ρ (fun hxy => hyx hxy.symm) v] at hw
    exact h y w hw

/-- One binding per variable of a list, taken from a list of pure values, keeps
the environment pure. -/
theorem PureEnv.extendAll : ∀ (xs : List Var) (ρ : Env) (vs : List Expr),
    PureEnv ρ → (∀ v ∈ vs, Pure v) → PureEnv (Env.extendAll ρ xs vs)
  | [], _, _, h, _ => h
  | _ :: _, _, [], h, _ => h
  | x :: xs, ρ, v :: vs, h, hvs =>
      PureEnv.extendAll xs (Env.extend ρ x v) vs (PureEnv.extend h (hvs v (by simp)))
        (fun w hw => hvs w (by simp [hw]))

/-- An environment binds a pure value for every bound variable. -/
theorem PureEnv.get? {ρ : Env} {x : Var} {v : Expr} (h : PureEnv ρ)
    (hx : Env.get? ρ x = some v) : Pure v := h x v hx

/-! ## The reduction

The redexes of Figure 6 (`Root`) and the same rules with one congruence rule per
context former (`Step`). -/

/-- A redex: the rules of Figure 6 at the root of a term. -/
inductive Root : Env → Expr → Env → Expr → Prop where
  /-- `(λx. body) v ⟶ body`, the environment extended with the binding. -/
  | beta {ρ x body v} : Value v → Root ρ (.app (.lam x body) v) (Env.extend ρ x v) body
  /-- `x v` where `x` names an abstraction: the paper's `(λx. body) v` reached
  through the environment. -/
  | betaVar {ρ x y body v} : Env.get? ρ x = some (.lam y body) → Value v →
      Root ρ (.app (.var x) v) (Env.extend ρ y v) body
  /-- `val x = v; body ⟶ body`, the environment extended with the binding. -/
  | bindVal {ρ x v body} : Value v → Root ρ (.bind x v body) (Env.extend ρ x v) body
  /-- `match x { c ys → body }` where `x` names a node written at the tag `c`: the
  arm's binders bound to the node's fields. -/
  | matchVal {ρ x c ys body n} : Env.get? ρ x = some n → nodeTag? n = some c →
      ys.length = (nodeFields n).length →
      Root ρ (.matchC x c ys body) (Env.extendAll ρ ys (nodeFields n)) body
  /-- The write: the node `x` names has slot `i` set to the value `v`. -/
  | storeVal {ρ x i v n n'} : Env.get? ρ x = some n → Value n → Value v →
      slotUpdate n i v = some n' → Root ρ (.store x i v) ρ n'

/-- The reduction of the source calculus: a redex, or a step of a subterm in one
of the paper's contexts. The comment at the top of the module says why there is
no rule for the fields of a node or the binders of a match: those are not
evaluation positions in the paper's contexts. -/
inductive Step : Env → Expr → Env → Expr → Prop where
  /-- A redex is a step. -/
  | root {ρ e ρ' e'} : Root ρ e ρ' e' → Step ρ e ρ' e'
  /-- A step in the function position of an application. -/
  | appFun {ρ f ρ' f' a} : Step ρ f ρ' f' → Step ρ (.app f a) ρ' (.app f' a)
  /-- A step in the argument of an application whose function is a value. -/
  | appArg {ρ f a ρ' a'} : Value f → Step ρ a ρ' a' → Step ρ (.app f a) ρ' (.app f a')
  /-- A step in the bound term of a binding. -/
  | bindFun {ρ e₁ ρ' e₁' x e₂} : Step ρ e₁ ρ' e₁' → Step ρ (.bind x e₁ e₂) ρ' (.bind x e₁' e₂)

/-- A redex is a step. -/
theorem Root.toStep {ρ e ρ' e'} (h : Root ρ e ρ' e') : Step ρ e ρ' e' := Step.root h

/-! ## No value steps

The observation every overlap in the determinism proof below is separated by. -/

/-- A value does not step. -/
theorem value_no_step : ∀ {ρ e ρ' e'}, Step ρ e ρ' e' → Value e → False := by
  intro ρ e ρ' e' hs
  induction hs with
  | root hr => intro hv; cases hr <;> cases hv
  | appFun hs ih => intro hv; cases hv
  | appArg hf hs ih => intro hv; cases hv
  | bindFun hs ih => intro hv; cases hv

/-- An abstraction does not step. -/
@[simp] theorem no_step_lam {ρ : Env} {x : Var} {body : Expr} {ρ' : Env} {e' : Expr} :
    ¬ Step ρ (.lam x body) ρ' e' := fun h => value_no_step h (Value.lam x body)

/-- A variable does not step. -/
@[simp] theorem no_step_var {ρ : Env} {x : Var} {ρ' : Env} {e' : Expr} :
    ¬ Step ρ (.var x) ρ' e' := fun h => value_no_step h (Value.var x)

/-- A nullary node does not step. -/
@[simp] theorem no_step_con0 {ρ : Env} {c : Ctor} {ρ' : Env} {e' : Expr} :
    ¬ Step ρ (.con0 c) ρ' e' := fun h => value_no_step h (Value.con0 c)

/-! ## Determinism -/

/-- Two redexes of one configuration agree: the environment and the contractum
are both unique. -/
theorem root_deterministic : ∀ {ρ e ρ₁ e₁ ρ₂ e₂}, Root ρ e ρ₁ e₁ → Root ρ e ρ₂ e₂ →
    ρ₁ = ρ₂ ∧ e₁ = e₂ := by
  intro ρ e ρ₁ e₁ ρ₂ e₂ h₁
  cases h₁ with
  | beta hv =>
      intro h₂
      cases h₂ with
      | beta _ => exact ⟨rfl, rfl⟩
  | betaVar hl hv =>
      intro h₂
      cases h₂ with
      | betaVar hl' hv' =>
          rw [hl] at hl'
          cases hl'
          exact ⟨rfl, rfl⟩
  | bindVal hv =>
      intro h₂
      cases h₂ with
      | bindVal _ => exact ⟨rfl, rfl⟩
  | matchVal hl ht hlen =>
      intro h₂
      cases h₂ with
      | matchVal hl' ht' hlen' =>
          rw [hl] at hl'
          cases hl'
          rw [ht] at ht'
          cases ht'
          exact ⟨rfl, rfl⟩
  | storeVal hl hn hv hsu =>
      intro h₂
      cases h₂ with
      | storeVal hl' hn' hv' hsu' =>
          rw [hl] at hl'
          cases hl'
          rw [hsu] at hsu'
          exact ⟨rfl, Option.some.inj hsu'⟩

/-- A configuration has at most one step: the environment and the contractum are
both unique. -/
theorem step_deterministic : ∀ {ρ e ρ₁ e₁}, Step ρ e ρ₁ e₁ →
    ∀ {ρ₂ e₂}, Step ρ e ρ₂ e₂ → ρ₁ = ρ₂ ∧ e₁ = e₂ := by
  intro ρ e ρ₁ e₁ h₁
  induction h₁ with
  | root hr =>
      cases hr with
      | beta hv =>
          intro ρ₂ e₂ h₂
          cases h₂ with
          | root hr' => exact root_deterministic (Root.beta hv) hr'
          | appFun hs => exact (no_step_lam hs).elim
          | appArg hv' hs => exact (value_no_step hs hv).elim
      | betaVar hl hv =>
          intro ρ₂ e₂ h₂
          cases h₂ with
          | root hr' => exact root_deterministic (Root.betaVar hl hv) hr'
          | appFun hs => exact (no_step_var hs).elim
          | appArg hv' hs => exact (value_no_step hs hv).elim
      | bindVal hv =>
          intro ρ₂ e₂ h₂
          cases h₂ with
          | root hr' => exact root_deterministic (Root.bindVal hv) hr'
          | bindFun hs => exact (value_no_step hs hv).elim
      | matchVal hl ht hlen =>
          intro ρ₂ e₂ h₂
          cases h₂ with
          | root hr' => exact root_deterministic (Root.matchVal hl ht hlen) hr'
      | storeVal hl hn hv hsu =>
          intro ρ₂ e₂ h₂
          cases h₂ with
          | root hr' => exact root_deterministic (Root.storeVal hl hn hv hsu) hr'
  | appFun hs ih =>
      intro ρ₂ e₂ h₂
      cases h₂ with
      | root hr' =>
          cases hr' with
          | beta hv => exact (no_step_lam hs).elim
          | betaVar hl hv => exact (no_step_var hs).elim
      | appFun hs' =>
          obtain ⟨hρ, hf⟩ := ih hs'
          exact ⟨hρ, by rw [hf]⟩
      | appArg hf hs' => exact (value_no_step hs hf).elim
  | appArg hf hs ih =>
      intro ρ₂ e₂ h₂
      cases h₂ with
      | root hr' =>
          cases hr' with
          | beta hv => exact (value_no_step hs hv).elim
          | betaVar hl hv => exact (value_no_step hs hv).elim
      | appFun hs' => exact (value_no_step hs' hf).elim
      | appArg hf' hs' =>
          obtain ⟨hρ, ha⟩ := ih hs'
          exact ⟨hρ, by rw [ha]⟩
  | bindFun hs ih =>
      intro ρ₂ e₂ h₂
      cases h₂ with
      | root hr' =>
          cases hr' with
          | bindVal hv => exact (value_no_step hs hv).elim
      | bindFun hs' =>
          obtain ⟨hρ, he⟩ := ih hs'
          exact ⟨hρ, by rw [he]⟩

/-! ## The evaluation contexts

The paper's contexts `□`, `E e`, `v E` and `val x = E; e`, their plugging, and
the theorem that `Step` is exactly the closure of `Root` under them. -/

/-- An evaluation context: a term with one hole, in the positions the reduction
of the source calculus reaches. -/
inductive Ectx where
  /-- The hole. -/
  | hole
  /-- `E a`, the function position of an application. -/
  | appL (E : Ectx) (a : Expr)
  /-- `f E`, the argument position of an application. -/
  | appR (f : Expr) (E : Ectx)
  /-- `val x = E; e₂`, the bound term of a binding. -/
  | bindL (x : Var) (E : Ectx) (e₂ : Expr)

/-- A context's hole filled with a term. -/
def Ectx.plug : Ectx → Expr → Expr
  | .hole, e => e
  | .appL E a, e => .app (E.plug e) a
  | .appR f E, e => .app f (E.plug e)
  | .bindL x E e₂, e => .bind x (E.plug e) e₂

/-- The contexts whose surrounding terms are values where a rule requires one:
stepping the argument of an application needs its function to be a value, and a
context with a hole in that position has to keep that. -/
inductive Ectx.WF : Ectx → Prop where
  /-- The hole is well formed. -/
  | hole : WF .hole
  /-- The function position of an application may hold any context. -/
  | appL {E a} : WF E → WF (.appL E a)
  /-- The argument position of an application requires a value function. -/
  | appR {f E} : Value f → WF E → WF (.appR f E)
  /-- The bound term of a binding may hold any context. -/
  | bindL {x E e₂} : WF E → WF (.bindL x E e₂)

/-- A redex inside a well-formed context is a step: the paper's `E[e] ⟶ E[e']`
read as the congruence rules `Step` has, one per context former. -/
theorem step_of_plug : ∀ {E : Ectx} {ρ r ρ' r'}, Ectx.WF E → Root ρ r ρ' r' →
    Step ρ (E.plug r) ρ' (E.plug r') := by
  intro E
  induction E with
  | hole => intro ρ r ρ' r' _ hroot; exact hroot.toStep
  | appL E a ih =>
      intro ρ r ρ' r' hwf hroot
      exact Step.appFun (ih (by cases hwf with | appL h => exact h) hroot)
  | appR f E ih =>
      intro ρ r ρ' r' hwf hroot
      cases hwf with
      | appR hf h => exact Step.appArg hf (ih h hroot)
  | bindL x E e₂ ih =>
      intro ρ r ρ' r' hwf hroot
      cases hwf with
      | bindL h => exact Step.bindFun (ih h hroot)

/-- A decomposition of a step in the function position, carried over to the
application it sits in: the function's context becomes the application's function
position. -/
theorem ectx_appFun {ρ : Env} {f : Expr} {ρ' : Env} {f' a : Expr} {E : Ectx} {r r' : Expr}
    (hwf : Ectx.WF E) (hr : Root ρ r ρ' r') (he : f = E.plug r) (he' : f' = E.plug r') :
    ∃ E' r₀ r₀', Ectx.WF E' ∧ Root ρ r₀ ρ' r₀' ∧ (.app f a) = E'.plug r₀ ∧
      (.app f' a) = E'.plug r₀' :=
  ⟨Ectx.appL E a, r, r', Ectx.WF.appL hwf, hr, by rw [he]; rfl, by rw [he']; rfl⟩

/-- A decomposition of a step in the argument of an application whose function is
a value, carried over to the application it sits in: the argument's context
becomes the application's argument position. -/
theorem ectx_appArg {ρ : Env} {f a : Expr} {ρ' : Env} {a' : Expr} {E : Ectx} {r r' : Expr}
    (hf : Value f) (hwf : Ectx.WF E) (hr : Root ρ r ρ' r') (he : a = E.plug r)
    (he' : a' = E.plug r') :
    ∃ E' r₀ r₀', Ectx.WF E' ∧ Root ρ r₀ ρ' r₀' ∧ (.app f a) = E'.plug r₀ ∧
      (.app f a') = E'.plug r₀' :=
  ⟨Ectx.appR f E, r, r', Ectx.WF.appR hf hwf, hr, by rw [he]; rfl, by rw [he']; rfl⟩

/-- A decomposition of a step in the bound term of a binding, carried over to the
binding it sits in: the bound term's context becomes the binding's bound
position. -/
theorem ectx_bindFun {ρ : Env} {x : Var} {e₁ : Expr} {ρ' : Env} {e₁' e₂ : Expr}
    {E : Ectx} {r r' : Expr}
    (hwf : Ectx.WF E) (hr : Root ρ r ρ' r') (he : e₁ = E.plug r) (he' : e₁' = E.plug r') :
    ∃ E' r₀ r₀', Ectx.WF E' ∧ Root ρ r₀ ρ' r₀' ∧ (.bind x e₁ e₂) = E'.plug r₀ ∧
      (.bind x e₁' e₂) = E'.plug r₀' :=
  ⟨Ectx.bindL x E e₂, r, r', Ectx.WF.bindL hwf, hr, by rw [he]; rfl, by rw [he']; rfl⟩

/-- Every step is a redex inside a well-formed evaluation context. -/
theorem step_to_ectx : ∀ {ρ e ρ' e'}, Step ρ e ρ' e' →
    ∃ E r r', Ectx.WF E ∧ Root ρ r ρ' r' ∧ e = E.plug r ∧ e' = E.plug r' := by
  intro ρ e ρ' e' hs
  induction hs with
  | root hr => exact ⟨.hole, _, _, Ectx.WF.hole, hr, rfl, rfl⟩
  | appFun hs ih =>
      obtain ⟨E, r, r', hwf, hr, he, he'⟩ := ih
      exact ectx_appFun hwf hr he he'
  | appArg hf hs ih =>
      obtain ⟨E, r, r', hwf, hr, he, he'⟩ := ih
      exact ectx_appArg hf hwf hr he he'
  | bindFun hs ih =>
      obtain ⟨E, r, r', hwf, hr, he, he'⟩ := ih
      exact ectx_bindFun hwf hr he he'

/-- A step is exactly a redex inside a well-formed evaluation context. -/
theorem step_iff_ectx {ρ e ρ' e'} :
    Step ρ e ρ' e' ↔ ∃ E r r', Ectx.WF E ∧ Root ρ r ρ' r' ∧ e = E.plug r ∧ e' = E.plug r' :=
  ⟨step_to_ectx, fun ⟨E, r, r', hwf, hr, he, he'⟩ => by
    rw [he, he']
    exact step_of_plug hwf hr⟩

/-! ## The evaluator the checks guard on

A structural, deterministic evaluator: the root rules at the configuration, then
the leftmost-outermost step of a subterm, and `none` when the configuration is
stuck. Its soundness is what makes a `#guard` on it a statement about `Step`. -/

/-- The root rules tried at a configuration: the redex of the configuration's own
shape, or `none` when the configuration is not a redex. -/
def rootStep? (ρ : Env) : Expr → Option (Env × Expr)
  | .var _ => none
  | .lam _ _ => none
  | .app f a =>
      match f with
      | .lam x body => if valueB a then some (Env.extend ρ x a, body) else none
      | .var x =>
          match Env.get? ρ x with
          | some (.lam y body) => if valueB a then some (Env.extend ρ y a, body) else none
          | _ => none
      | _ => none
  | .bind x e₁ e₂ => if valueB e₁ then some (Env.extend ρ x e₁, e₂) else none
  | .matchC x c ys body =>
      match Env.get? ρ x with
      | some n =>
          match nodeTag? n with
          | some d =>
              if d = c ∧ ys.length = (nodeFields n).length then
                some (Env.extendAll ρ ys (nodeFields n), body)
              else none
          | none => none
      | none => none
  | .dup _ _ => none
  | .drop _ _ => none
  | .con0 _ => none
  | .con1 _ _ => none
  | .con2 _ _ _ => none
  | .store x i v =>
      match Env.get? ρ x with
      | some n =>
          if valueB n ∧ valueB v then (slotUpdate n i v).map (fun n' => (ρ, n')) else none
      | none => none

/-- The leftmost-outermost step of a configuration, or `none` when it is stuck:
the root rules first, then a step in the function position of an application, in
the argument of an application whose function is a value, or in the bound term of
a binding. The recursion is structural on the term, so the kernel reduces the
evaluator at a concrete configuration. -/
def step? (ρ : Env) : Expr → Option (Env × Expr)
  | .var x => rootStep? ρ (.var x)
  | .lam x body => rootStep? ρ (.lam x body)
  | .app f a =>
      match rootStep? ρ (.app f a) with
      | some q => some q
      | none =>
          match step? ρ f with
          | some q => some (q.1, .app q.2 a)
          | none => if valueB f then (step? ρ a).map (fun q => (q.1, .app f q.2)) else none
  | .bind x e₁ e₂ =>
      match rootStep? ρ (.bind x e₁ e₂) with
      | some q => some q
      | none => (step? ρ e₁).map (fun q => (q.1, .bind x q.2 e₂))
  | .matchC x c ys body => rootStep? ρ (.matchC x c ys body)
  | .dup x e => rootStep? ρ (.dup x e)
  | .drop x e => rootStep? ρ (.drop x e)
  | .con0 c => rootStep? ρ (.con0 c)
  | .con1 c a => rootStep? ρ (.con1 c a)
  | .con2 c a b => rootStep? ρ (.con2 c a b)
  | .store x i v => rootStep? ρ (.store x i v)

/-- The root part of the evaluator computes only redexes of `Root`. -/
theorem rootStep?_sound (ρ : Env) : ∀ {e ρ' e'}, rootStep? ρ e = some (ρ', e') →
    Root ρ e ρ' e' := by
  intro e
  cases e with
  | var x => intro ρ' e' h; simp [rootStep?] at h
  | lam x body => intro ρ' e' h; simp [rootStep?] at h
  | app f a =>
      cases f with
      | var x =>
          intro ρ' e' h
          cases hl : Env.get? ρ x with
          | none => simp [rootStep?, hl] at h
          | some w =>
              cases w with
              | lam y body =>
                  by_cases hv : valueB a = true
                  · simp [rootStep?, hl, hv, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hρ, he⟩ := h
                    rw [← hρ, ← he]
                    exact Root.betaVar hl ((valueB_iff a).mp hv)
                  · simp [rootStep?, hl, hv] at h
              | var z => simp [rootStep?, hl] at h
              | app g b => simp [rootStep?, hl] at h
              | bind z e₁ e₂ => simp [rootStep?, hl] at h
              | matchC z c ys b => simp [rootStep?, hl] at h
              | dup z ez => simp [rootStep?, hl] at h
              | drop z ez => simp [rootStep?, hl] at h
              | con0 z => simp [rootStep?, hl] at h
              | con1 z a' => simp [rootStep?, hl] at h
              | con2 z a' b' => simp [rootStep?, hl] at h
              | store z i' v' => simp [rootStep?, hl] at h
      | lam x body =>
          intro ρ' e' h
          by_cases hv : valueB a = true
          · simp [rootStep?, hv, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hρ, he⟩ := h
            rw [← hρ, ← he]
            exact Root.beta ((valueB_iff a).mp hv)
          · simp [rootStep?, hv] at h
      | app g b => intro ρ' e' h; simp [rootStep?] at h
      | bind z e₁ e₂ => intro ρ' e' h; simp [rootStep?] at h
      | matchC z c ys b => intro ρ' e' h; simp [rootStep?] at h
      | dup z ez => intro ρ' e' h; simp [rootStep?] at h
      | drop z ez => intro ρ' e' h; simp [rootStep?] at h
      | con0 z => intro ρ' e' h; simp [rootStep?] at h
      | con1 z a' => intro ρ' e' h; simp [rootStep?] at h
      | con2 z a' b' => intro ρ' e' h; simp [rootStep?] at h
      | store z i' v' => intro ρ' e' h; simp [rootStep?] at h
  | bind x e₁ e₂ =>
      intro ρ' e' h
      by_cases hv : valueB e₁ = true
      · simp [rootStep?, hv, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hρ, he⟩ := h
        rw [← hρ, ← he]
        exact Root.bindVal ((valueB_iff e₁).mp hv)
      · simp [rootStep?, hv] at h
  | matchC x c ys body =>
      intro ρ' e' h
      cases hl : Env.get? ρ x with
      | none => simp [rootStep?, hl] at h
      | some n =>
          cases ht : nodeTag? n with
          | none => simp [rootStep?, hl, ht] at h
          | some d =>
              by_cases hc : d = c ∧ ys.length = (nodeFields n).length
              · simp [rootStep?, hl, ht, hc, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨hρ, he⟩ := h
                rw [← hρ, ← he]
                obtain ⟨hdc, hlen⟩ := hc
                rw [hdc] at ht
                exact Root.matchVal hl ht hlen
              · simp [rootStep?, hl, ht, ite_eq_right hc] at h
  | dup x ex => intro ρ' e' h; simp [rootStep?] at h
  | drop x ex => intro ρ' e' h; simp [rootStep?] at h
  | con0 c => intro ρ' e' h; simp [rootStep?] at h
  | con1 c a => intro ρ' e' h; simp [rootStep?] at h
  | con2 c a b => intro ρ' e' h; simp [rootStep?] at h
  | store x i v =>
      intro ρ' e' h
      cases hl : Env.get? ρ x with
      | none => simp [rootStep?, hl] at h
      | some n =>
          by_cases hc : valueB n ∧ valueB v
          · simp [rootStep?, hl, hc] at h
            cases hsu : slotUpdate n i v with
            | none => rw [hsu] at h; simp at h
            | some n'' =>
                rw [hsu] at h
                simp [Option.some.injEq] at h
                obtain ⟨hρ, he⟩ := h
                rw [← hρ, ← he]
                exact Root.storeVal hl ((valueB_iff n).mp hc.1) ((valueB_iff v).mp hc.2) hsu
          · simp [rootStep?, hl, ite_eq_right hc] at h

/-- The evaluator computes only steps of `Step`. The recursion is structural on
the term, which is what lets a `#guard` on the evaluator be a statement about
`Step`. -/
theorem step?_sound (ρ : Env) : ∀ (e : Expr) (ρ' : Env) (e' : Expr),
    step? ρ e = some (ρ', e') → Step ρ e ρ' e'
  | .var x, ρ', e', h => by
      simp only [step?] at h
      exact Step.root (rootStep?_sound ρ h)
  | .lam x body, ρ', e', h => by
      simp only [step?] at h
      exact Step.root (rootStep?_sound ρ h)
  | .app f a, ρ', e', h => by
      cases hr : rootStep? ρ (.app f a) with
      | some q =>
          simp only [step?, hr] at h
          cases h
          exact Step.root (rootStep?_sound ρ hr)
      | none =>
          simp only [step?, hr] at h
          cases hf : step? ρ f with
          | some q =>
              rw [hf] at h
              cases h
              exact Step.appFun (step?_sound ρ f q.1 q.2 hf)
          | none =>
              rw [hf] at h
              by_cases hv : valueB f
              · rw [ite_eq_left hv] at h
                cases ha : step? ρ a with
                | none => rw [ha] at h; simp at h
                | some q =>
                    rw [ha] at h
                    cases h
                    exact Step.appArg ((valueB_iff f).mp hv) (step?_sound ρ a q.1 q.2 ha)
              · rw [ite_eq_right hv] at h
                simp at h
  | .bind x e₁ e₂, ρ', e', h => by
      cases hr : rootStep? ρ (.bind x e₁ e₂) with
      | some q =>
          simp only [step?, hr] at h
          cases h
          exact Step.root (rootStep?_sound ρ hr)
      | none =>
          simp only [step?, hr] at h
          cases hf : step? ρ e₁ with
          | none => rw [hf] at h; simp at h
          | some q =>
              rw [hf] at h
              cases h
              exact Step.bindFun (step?_sound ρ e₁ q.1 q.2 hf)
  | .matchC x c ys body, ρ', e', h => by
      simp only [step?] at h
      exact Step.root (rootStep?_sound ρ h)
  | .dup x e, ρ', e', h => by
      simp only [step?] at h
      exact Step.root (rootStep?_sound ρ h)
  | .drop x e, ρ', e', h => by
      simp only [step?] at h
      exact Step.root (rootStep?_sound ρ h)
  | .con0 c, ρ', e', h => by
      simp only [step?] at h
      exact Step.root (rootStep?_sound ρ h)
  | .con1 c a, ρ', e', h => by
      simp only [step?] at h
      exact Step.root (rootStep?_sound ρ h)
  | .con2 c a b, ρ', e', h => by
      simp only [step?] at h
      exact Step.root (rootStep?_sound ρ h)
  | .store x i v, ρ', e', h => by
      simp only [step?] at h
      exact Step.root (rootStep?_sound ρ h)

/-! ## Purity along an evaluation path

A term of the source fragment is reduced only by rules whose contracta are
subterms of the term or bindings of the environment, and both stay pure: the
fragment has no resource operation on any path. -/

/-- The reflexive-transitive closure of the reduction: an evaluation path. -/
inductive StepStar : Env → Expr → Env → Expr → Prop where
  /-- A configuration evaluates to itself. -/
  | refl (ρ : Env) (e : Expr) : StepStar ρ e ρ e
  /-- One step and the rest of the path. -/
  | step {ρ e ρ' e' ρ'' e''} : Step ρ e ρ' e' → StepStar ρ' e' ρ'' e'' →
      StepStar ρ e ρ'' e''

/-- A step of a pure term under a pure environment leaves a pure term and a pure
environment: the source fragment is closed under reduction. -/
theorem step_preserves_pure {ρ e ρ' e'} (hs : Step ρ e ρ' e') :
    Pure e → PureEnv ρ → Pure e' ∧ PureEnv ρ' := by
  induction hs with
  | root hr =>
      intro he hρ
      cases hr with
      | beta hv =>
          obtain ⟨hlam, hv'⟩ := (pure_app_iff _ _).mp he
          exact ⟨(pure_lam_iff _ _).mp hlam, hρ.extend hv'⟩
      | betaVar hl hv =>
          obtain ⟨_, hv'⟩ := (pure_app_iff _ _).mp he
          exact ⟨(pure_lam_iff _ _).mp (hρ.get? hl), hρ.extend hv'⟩
      | bindVal hv =>
          obtain ⟨hv', hbody⟩ := (pure_bind_iff _ _ _).mp he
          exact ⟨hbody, hρ.extend hv'⟩
      | matchVal hl ht hlen =>
          have hnode : Pure _ := hρ.get? hl
          exact ⟨(pure_matchC_iff _ _ _ _).mp he,
            PureEnv.extendAll _ _ _ hρ (nodeFields_pure hnode)⟩
      | storeVal hl hn hv hsu =>
          exact ⟨slotUpdate_pure (hρ.get? hl) ((pure_store_iff _ _ _).mp he) hsu, hρ⟩
  | appFun hs ih =>
      intro he hρ
      obtain ⟨hf, ha⟩ := (pure_app_iff _ _).mp he
      obtain ⟨hf', hρ'⟩ := ih hf hρ
      exact ⟨(pure_app_iff _ _).mpr ⟨hf', ha⟩, hρ'⟩
  | appArg hf hs ih =>
      intro he hρ
      obtain ⟨hfun, ha⟩ := (pure_app_iff _ _).mp he
      obtain ⟨ha', hρ'⟩ := ih ha hρ
      exact ⟨(pure_app_iff _ _).mpr ⟨hfun, ha'⟩, hρ'⟩
  | bindFun hs ih =>
      intro he hρ
      obtain ⟨h₁, h₂⟩ := (pure_bind_iff _ _ _).mp he
      obtain ⟨h₁', hρ'⟩ := ih h₁ hρ
      exact ⟨(pure_bind_iff _ _ _).mpr ⟨h₁', h₂⟩, hρ'⟩

/-- Along any evaluation path a pure term stays pure and so does the environment:
no `dup` and no `drop` appears, and the fragment is closed. -/
theorem pure_steps_pure {ρ e ρ' e'} (hs : StepStar ρ e ρ' e') :
    Pure e → PureEnv ρ → Pure e' ∧ PureEnv ρ' := by
  induction hs with
  | refl => intro he hρ; exact ⟨he, hρ⟩
  | step hstep _ ih =>
      intro he hρ
      obtain ⟨he', hρ'⟩ := step_preserves_pure hstep he hρ
      exact ih he' hρ'

end Scidonia.RC
