/-
The source semantics: a strict, deterministic small-step reduction of the
calculus of `Scidonia.RC.Syntax`, and the purity preservation that makes the
source fragment worth naming.

Reinking, Xie, de Moura and Leijen, *Perceus: Garbage Free Reference Counting
with Reuse* (PLDI 2021), Figure 6 gives the source calculus's reduction as
`E[e] ⟶ E[e']` over redexes

* `(λx. e) v ⟶ e[x := v]`,
* `val x = v; e ⟶ e[x := v]`,
* `case C v̄ { C ȳ → e } ⟶ e[ȳ := v̄]`, and
* the write: the node the subject is has slot `i` set to the value `v`,

with `E` ranging over the evaluation contexts `□`, `E e`, `v E` and
`val x = E; e`. This module writes those redexes as the judgement `Root`, the
same rules plus one congruence rule per context former as the judgement `Step`,
and proves `step_iff_ectx`: a step is exactly a redex inside a well-formed
evaluation context (`Ectx.plug`). The congruence rules are the paper's
`E[e] ⟶ E[e']` written rule by rule, so the two judgements are two views of one
relation rather than two semantics.

**Substitution, and no environment.** A configuration is a term, and the rules
are the paper's substitution rules: a binder replaces its variable — the
abstraction's body, the bound term, the arm's binders — by the value it carries
(`subst`, `substAll`), so a variable is resolved at the moment a binder
introduces it and nothing is looked up again later. That is what makes the
reduction capture-avoiding: the free variables of an abstraction are substituted
before any later binder of the same name exists, so a later `val x = ...` cannot
change what an earlier `(λy. ...)` computes. There is no environment and no rule
that resolves a variable in function position: a variable there is a variable,
not a function.

**The subjects are terms.** The subject of a match and of a write is a term,
which is what λ¹'s metasyntax has in that position — the paper's rule is
`case e { C ȳ → e′ }`, over a metavariable the substitution resolves. An encoding
whose subject is a *name* cannot carry that substitution at all, because
substitution replaces a variable by a term and a name position holds no term, so
the syntax holds a term (`Scidonia.RC.Syntax` records the choice). The cost is
that the subject's variables are variables of the term: an A-normal source writes
`store (var y) 1 v`, the binding that introduces `y` substitutes the node in, and
an ownership account of the subject reads its occurrences from the term rather
than from a name lookup. The environment machinery an earlier form of this module
carried (`Env`, `PureEnv`, their lemmas and the rule that resolved a variable in
function position) is *deleted*, not kept beside the substitution.

**A-normal form.** λ¹ is an A-normal-form calculus: the argument of an
application, the subject of a match, the subject of a write and the value of a
write are *values*, and the computation that produces them is sequenced by `val`
bindings. The *redex* of an application is available only when its argument is a
value; when the function is a value and the argument is not, the step relation
still steps the argument (`Step.appArg`), so such a configuration has a step and
is not stuck. The same reading forbids a redex for a match whose subject is not a
node and for a write whose subject is not a node or whose value is not a value.
`Step` therefore has a congruence rule for the function position of an
application, for the argument position of an application whose function is a
value, and for the bound term of a binding, and none for the subject of a match,
the subject of a write, the fields of a node or the binders of a match: the
paper's contexts do not descend into those positions, and the A-normal form has
already produced their values by a `val` binding. A source term that is not in
that shape is a term this module has no step for, and the lowering of
`Scidonia.RC.Lower` is what puts a term into it.

**The write.** At the source the write is *functional*: it reduces to the node
the subject is, with slot `i` replaced by `v`, a value. Nothing here is destructive
and nothing here has a reference count; whether the target's write updates in
place is a property of the target calculus and its count, which this slice does
not build. What the source fixes is the shape of the result.

## What is proved

* `valueB_iff`: the decidable test of valuehood agrees with `Value`; the shapes
  that are never values are separated out (`not_value_app` and the rest), and
  `value_canonical` says every value is a variable, an abstraction or a node.
* `value_no_step`: no value steps — the observation every overlap in the
  determinism proof is separated by, and there are no others.
* `root_deterministic` and `step_deterministic`: a configuration has at most one
  step, and the contractum of a redex is unique.
* `step_iff_ectx`: a step is a redex inside a well-formed evaluation context, and
  conversely, which is the paper's `E[e] ⟶ E[e']` for this syntax.
* `subst_pure` and `substAll_pure`: the substitution the rules are written with
  preserves the source fragment, which is what the environment's purity
  condition was for.
* `rootStep?_sound` and `step?_sound`: the evaluator the checks guard on computes
  only steps of `Step`. It is written structurally on the term, so a `#guard` can
  evaluate it. `run` is that evaluator under a fuel, and `run_stepStar` says
  every term it reaches is reached by `StepStar`, so a guarded value is a fact
  about the reduction.
* `StepStar` and `pure_steps_pure`: along any evaluation path a term of the
  source fragment stays in the fragment — no `dup` and no `drop` ever appears.
  That is the erasure sanity fact the fragment is for and what the lowering is
  read against.

## What is modelled, and what is trusted

λ¹ is a calculus of *closed* terms and this module reduces closed configurations.
No rule of the reduction resolves a free variable: the rules substitute only for
the variable a binder introduces, so a variable that is free in a configuration
is never bound by a step, and a subject position that holds a variable rather
than a node has no redex and is stuck. Capture-avoidance rests on that
discipline, since a value substituted for a variable is a subterm of a closed
configuration and so has no free variable for a binder to capture; the module
does not carry a closedness predicate, and an open term is outside the
discipline this reduction is stated for.

A node's fields are read with `nodeFields`: none for a nullary node, one for a
unary node and two for a binary one, and an arm binds the variables it names to
the fields in order, which the match rule admits only when the two lists are the
same length. A write's slot index is a natural number and `slotUpdate` answers
`none` outside a node's slots, so a write at a slot a node does not have is
stuck; the subject and the written value are required to be values, so a write's
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
@[simp] theorem not_value_matchC (s : Expr) (c : Ctor) (ys : List Var) (body : Expr) :
    ¬ Value (.matchC s c ys body) := by
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
@[simp] theorem not_value_store (s : Expr) (i : Nat) (v : Expr) : ¬ Value (.store s i v) := by
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
  | .matchC s c ys body =>
      Iff.intro (fun h => absurd h (by simp [valueB]))
        (fun h => absurd h (not_value_matchC s c ys body))
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
  | .store s i v =>
      Iff.intro (fun h => absurd h (by simp [valueB])) (fun h => absurd h (not_value_store s i v))

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
  | matchC s c ys body => intro k hk; simp [nodeFields] at hk
  | dup x e => intro k hk; simp [nodeFields] at hk
  | drop x e => intro k hk; simp [nodeFields] at hk
  | store s i v => intro k hk; simp [nodeFields] at hk

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
  | matchC s c ys body => simp [slotUpdate] at h
  | dup x e => simp [slotUpdate] at h
  | drop x e => simp [slotUpdate] at h
  | con0 c => simp [slotUpdate] at h
  | store s i' v' => simp [slotUpdate] at h

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
  | matchC s c ys body => simp [slotUpdate] at h
  | dup x e => simp [slotUpdate] at h
  | drop x e => simp [slotUpdate] at h
  | store s i' v' => simp [slotUpdate] at h

/-! ## Substitution

The paper's `[x := v]`: where an environment form of this module threaded the
value each variable names and looked it up at a use, the rules here rewrite the
binder's body in place. -/

/-- The term `e` with every free occurrence of `x` replaced by the term `v`. A
binder of `x` stops the walk, and a binder of another name is walked under: the
step that inserts `v` is the only place a variable of `v` could be captured, and
the rules below insert a value of a closed configuration, which has no free
variable for a binder to capture. -/
def subst (x : Var) (v : Expr) : Expr → Expr
  | .var y => if y = x then v else .var y
  | .lam y body => if y = x then .lam y body else .lam y (subst x v body)
  | .app f a => .app (subst x v f) (subst x v a)
  | .bind y e₁ e₂ => .bind y (subst x v e₁) (if y = x then e₂ else subst x v e₂)
  | .matchC s c ys body =>
      .matchC (subst x v s) c ys (if x ∈ ys then body else subst x v body)
  | .dup y e => .dup y (subst x v e)
  | .drop y e => .drop y (subst x v e)
  | .con0 c => .con0 c
  | .con1 c a => .con1 c (subst x v a)
  | .con2 c a b => .con2 c (subst x v a) (subst x v b)
  | .store s i w => .store (subst x v s) i (subst x v w)

/-- A variable's own value is what is substituted for it. -/
@[simp] theorem subst_var_self (x : Var) (v : Expr) : subst x v (.var x) = v := by
  simp [subst]

/-- A variable under another name is left alone. -/
@[simp] theorem subst_var_of_ne {x y : Var} (h : y ≠ x) (v : Expr) :
    subst x v (.var y) = .var y := by
  simp [subst, h]

/-- Substitution preserves the source fragment: a variable of a pure term
replaced by a pure term leaves a pure term. This is what the environment's purity
condition (`PureEnv`, deleted with the environment) used to carry. -/
theorem subst_pure : ∀ (e : Expr) (x : Var) (v : Expr), Pure e → Pure v → Pure (subst x v e)
  | .var y, x, v, _, hv => by
      by_cases h : y = x
      · simpa [subst, h] using hv
      · simpa [subst, h] using Pure.var y
  | .lam y body, x, v, he, hv => by
      have hbody : Pure body := (pure_lam_iff y body).mp he
      by_cases h : y = x
      · simpa [subst, h] using Pure.lam hbody
      · simpa [subst, h] using Pure.lam (subst_pure body x v hbody hv)
  | .app f a, x, v, he, hv => by
      obtain ⟨hf, ha⟩ := (pure_app_iff f a).mp he
      simpa [subst] using Pure.app (subst_pure f x v hf hv) (subst_pure a x v ha hv)
  | .bind y e₁ e₂, x, v, he, hv => by
      obtain ⟨h₁, h₂⟩ := (pure_bind_iff y e₁ e₂).mp he
      by_cases h : y = x
      · simpa [subst, h] using Pure.bind (subst_pure e₁ x v h₁ hv) h₂
      · simpa [subst, h] using Pure.bind (subst_pure e₁ x v h₁ hv) (subst_pure e₂ x v h₂ hv)
  | .matchC s c ys body, x, v, he, hv => by
      obtain ⟨hs, hbody⟩ := (pure_matchC_iff s c ys body).mp he
      by_cases h : x ∈ ys
      · simpa [subst, h] using Pure.matchC (subst_pure s x v hs hv) hbody
      · simpa [subst, h] using Pure.matchC (subst_pure s x v hs hv) (subst_pure body x v hbody hv)
  | .dup y ex, _, _, he, _ => absurd he (not_pure_dup y ex)
  | .drop y ex, _, _, he, _ => absurd he (not_pure_drop y ex)
  | .con0 c, _, _, _, _ => by simpa [subst] using Pure.con0 c
  | .con1 c a, x, v, he, hv => by
      have ha : Pure a := (pure_con1_iff c a).mp he
      simpa [subst] using Pure.con1 (subst_pure a x v ha hv)
  | .con2 c a b, x, v, he, hv => by
      obtain ⟨ha, hb⟩ := (pure_con2_iff c a b).mp he
      simpa [subst] using Pure.con2 (subst_pure a x v ha hv) (subst_pure b x v hb hv)
  | .store s i w, x, v, he, hv => by
      obtain ⟨hs, hw⟩ := (pure_store_iff s i w).mp he
      simpa [subst] using Pure.store (subst_pure s x v hs hv) (subst_pure w x v hw hv)

/-- The term `e` with one variable replaced per pair, `ys` and `vs` walked
together: the first variable of `ys` is paired with the first term of `vs`. A
name paired more than once takes the value of its later pairing, because the
earlier pairing is applied to the result of the later one; an arm whose binders
name one variable twice is outside the discipline the source reads, and the
lists are read for their pairs rather than required to be distinct. -/
def substAll : List Var → List Expr → Expr → Expr
  | [], _, e => e
  | _ :: _, [], e => e
  | y :: ys, v :: vs, e => subst y v (substAll ys vs e)

/-- Substitution of many variables preserves the source fragment, when every term
substituted is pure. -/
theorem substAll_pure : ∀ (ys : List Var) (vs : List Expr) {e : Expr}, Pure e →
    (∀ v ∈ vs, Pure v) → Pure (substAll ys vs e)
  | [], _, _, he, _ => he
  | _ :: _, [], _, he, _ => he
  | y :: ys, v :: vs, e, he, hv =>
      subst_pure (substAll ys vs e) y v
        (substAll_pure ys vs he (fun w hw => hv w (by simp [hw])))
        (hv v (by simp))

/-! ## The reduction

The redexes of Figure 6 (`Root`) and the same rules with one congruence rule per
context former (`Step`). -/

/-- A redex: the rules of Figure 6 at the root of a term. -/
inductive Root : Expr → Expr → Prop where
  /-- `(λx. body) v ⟶ body[x := v]`. -/
  | beta {x : Var} {body v : Expr} : Value v → Root (.app (.lam x body) v) (subst x v body)
  /-- `val x = v; body ⟶ body[x := v]`. -/
  | bindVal {x : Var} {v body : Expr} : Value v → Root (.bind x v body) (subst x v body)
  /-- `match C v̄ { C ȳ → body } ⟶ body[ȳ := v̄]`: the subject is a value node, at
  the arm's tag and with the arm's number of fields. -/
  | matchVal {s : Expr} {c : Ctor} {ys : List Var} {body : Expr} : Value s →
      nodeTag? s = some c → ys.length = (nodeFields s).length →
      Root (.matchC s c ys body) (substAll ys (nodeFields s) body)
  /-- The write: the node the subject is has slot `i` set to the value `v`. -/
  | storeVal {s : Expr} {i : Nat} {v n' : Expr} : Value s → Value v →
      slotUpdate s i v = some n' → Root (.store s i v) n'

/-- The reduction of the source calculus: a redex, or a step of a subterm in one
of the paper's contexts. The comment at the top of the module says why there is
no rule for a match's subject, a write's subject, the fields of a node or the
binders of a match: those are not evaluation positions in the paper's contexts. -/
inductive Step : Expr → Expr → Prop where
  /-- A redex is a step. -/
  | root {e e' : Expr} : Root e e' → Step e e'
  /-- A step in the function position of an application. -/
  | appFun {f f' a : Expr} : Step f f' → Step (.app f a) (.app f' a)
  /-- A step in the argument of an application whose function is a value. -/
  | appArg {f a a' : Expr} : Value f → Step a a' → Step (.app f a) (.app f a')
  /-- A step in the bound term of a binding. -/
  | bindFun {e₁ e₁' : Expr} {x : Var} {e₂ : Expr} : Step e₁ e₁' →
      Step (.bind x e₁ e₂) (.bind x e₁' e₂)

/-- A redex is a step. -/
theorem Root.toStep {e e' : Expr} (h : Root e e') : Step e e' := Step.root h

/-! ## No value steps

The observation every overlap in the determinism proof below is separated by. -/

/-- A value does not step. -/
theorem value_no_step : ∀ {e e' : Expr}, Step e e' → Value e → False := by
  intro e e' hs
  induction hs with
  | root hr => intro hv; cases hr <;> cases hv
  | appFun hs ih => intro hv; cases hv
  | appArg hf hs ih => intro hv; cases hv
  | bindFun hs ih => intro hv; cases hv

/-- An abstraction does not step. -/
@[simp] theorem no_step_lam {x : Var} {body : Expr} {e' : Expr} :
    ¬ Step (.lam x body) e' := fun h => value_no_step h (Value.lam x body)

/-- A variable does not step. -/
@[simp] theorem no_step_var {x : Var} {e' : Expr} : ¬ Step (.var x) e' :=
  fun h => value_no_step h (Value.var x)

/-- A nullary node does not step. -/
@[simp] theorem no_step_con0 {c : Ctor} {e' : Expr} : ¬ Step (.con0 c) e' :=
  fun h => value_no_step h (Value.con0 c)

/-! ## Determinism -/

/-- Two redexes of one configuration agree: the contractum is unique. -/
theorem root_deterministic : ∀ {e e₁ e₂ : Expr}, Root e e₁ → Root e e₂ → e₁ = e₂ := by
  intro e e₁ e₂ h₁
  cases h₁ with
  | beta hv =>
      intro h₂
      cases h₂ with
      | beta _ => rfl
  | bindVal hv =>
      intro h₂
      cases h₂ with
      | bindVal _ => rfl
  | matchVal hs ht hlen =>
      intro h₂
      cases h₂ with
      | matchVal _ _ _ => rfl
  | storeVal hs hv hsu =>
      intro h₂
      cases h₂ with
      | storeVal _ _ hsu' =>
          rw [hsu] at hsu'
          exact Option.some.inj hsu'

/-- A configuration has at most one step: the contractum is unique. -/
theorem step_deterministic : ∀ {e e₁ : Expr}, Step e e₁ →
    ∀ {e₂ : Expr}, Step e e₂ → e₁ = e₂ := by
  intro e e₁ h₁
  induction h₁ with
  | root hr =>
      cases hr with
      | beta hv =>
          intro e₂ h₂
          cases h₂ with
          | root hr' => exact root_deterministic (Root.beta hv) hr'
          | appFun hs => exact (no_step_lam hs).elim
          | appArg hv' hs => exact (value_no_step hs hv).elim
      | bindVal hv =>
          intro e₂ h₂
          cases h₂ with
          | root hr' => exact root_deterministic (Root.bindVal hv) hr'
          | bindFun hs => exact (value_no_step hs hv).elim
      | matchVal hs ht hlen =>
          intro e₂ h₂
          cases h₂ with
          | root hr' => exact root_deterministic (Root.matchVal hs ht hlen) hr'
      | storeVal hs hv hsu =>
          intro e₂ h₂
          cases h₂ with
          | root hr' => exact root_deterministic (Root.storeVal hs hv hsu) hr'
  | appFun hs ih =>
      intro e₂ h₂
      cases h₂ with
      | root hr' =>
          cases hr' with
          | beta hv => exact (no_step_lam hs).elim
      | appFun hs' => rw [ih hs']
      | appArg hf hs' => exact (value_no_step hs hf).elim
  | appArg hf hs ih =>
      intro e₂ h₂
      cases h₂ with
      | root hr' =>
          cases hr' with
          | beta hv => exact (value_no_step hs hv).elim
      | appFun hs' => exact (value_no_step hs' hf).elim
      | appArg hf' hs' => rw [ih hs']
  | bindFun hs ih =>
      intro e₂ h₂
      cases h₂ with
      | root hr' =>
          cases hr' with
          | bindVal hv => exact (value_no_step hs hv).elim
      | bindFun hs' => rw [ih hs']

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
theorem step_of_plug : ∀ {E : Ectx} {r r' : Expr}, Ectx.WF E → Root r r' →
    Step (E.plug r) (E.plug r') := by
  intro E
  induction E with
  | hole => intro r r' _ hroot; exact hroot.toStep
  | appL E a ih =>
      intro r r' hwf hroot
      exact Step.appFun (ih (by cases hwf with | appL h => exact h) hroot)
  | appR f E ih =>
      intro r r' hwf hroot
      cases hwf with
      | appR hf h => exact Step.appArg hf (ih h hroot)
  | bindL x E e₂ ih =>
      intro r r' hwf hroot
      cases hwf with
      | bindL h => exact Step.bindFun (ih h hroot)

/-- A decomposition of a step in the function position, carried over to the
application it sits in: the function's context becomes the application's function
position. -/
theorem ectx_appFun {f : Expr} {f' a : Expr} {E : Ectx} {r r' : Expr}
    (hwf : Ectx.WF E) (hr : Root r r') (he : f = E.plug r) (he' : f' = E.plug r') :
    ∃ E' r₀ r₀', Ectx.WF E' ∧ Root r₀ r₀' ∧ (.app f a) = E'.plug r₀ ∧
      (.app f' a) = E'.plug r₀' :=
  ⟨Ectx.appL E a, r, r', Ectx.WF.appL hwf, hr, by rw [he]; rfl, by rw [he']; rfl⟩

/-- A decomposition of a step in the argument of an application whose function is
a value, carried over to the application it sits in: the argument's context
becomes the application's argument position. -/
theorem ectx_appArg {f a : Expr} {a' : Expr} {E : Ectx} {r r' : Expr}
    (hf : Value f) (hwf : Ectx.WF E) (hr : Root r r') (he : a = E.plug r)
    (he' : a' = E.plug r') :
    ∃ E' r₀ r₀', Ectx.WF E' ∧ Root r₀ r₀' ∧ (.app f a) = E'.plug r₀ ∧
      (.app f a') = E'.plug r₀' :=
  ⟨Ectx.appR f E, r, r', Ectx.WF.appR hf hwf, hr, by rw [he]; rfl, by rw [he']; rfl⟩

/-- A decomposition of a step in the bound term of a binding, carried over to the
binding it sits in: the bound term's context becomes the binding's bound
position. -/
theorem ectx_bindFun {x : Var} {e₁ : Expr} {e₁' e₂ : Expr} {E : Ectx} {r r' : Expr}
    (hwf : Ectx.WF E) (hr : Root r r') (he : e₁ = E.plug r) (he' : e₁' = E.plug r') :
    ∃ E' r₀ r₀', Ectx.WF E' ∧ Root r₀ r₀' ∧ (.bind x e₁ e₂) = E'.plug r₀ ∧
      (.bind x e₁' e₂) = E'.plug r₀' :=
  ⟨Ectx.bindL x E e₂, r, r', Ectx.WF.bindL hwf, hr, by rw [he]; rfl, by rw [he']; rfl⟩

/-- Every step is a redex inside a well-formed evaluation context. -/
theorem step_to_ectx : ∀ {e e' : Expr}, Step e e' →
    ∃ E r r', Ectx.WF E ∧ Root r r' ∧ e = E.plug r ∧ e' = E.plug r' := by
  intro e e' hs
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
theorem step_iff_ectx {e e' : Expr} :
    Step e e' ↔ ∃ E r r', Ectx.WF E ∧ Root r r' ∧ e = E.plug r ∧ e' = E.plug r' :=
  ⟨step_to_ectx, fun ⟨E, r, r', hwf, hr, he, he'⟩ => by
    rw [he, he']
    exact step_of_plug hwf hr⟩

/-! ## The evaluator the checks guard on

A structural, deterministic evaluator: the root rules at the term, then the
leftmost-outermost step of a subterm, and `none` when the configuration is stuck.
Its soundness is what makes a `#guard` on it a statement about `Step`. -/

/-- The root rules tried at a term: the redex of the term's own shape, or `none`
when the term is not a redex. -/
def rootStep? : Expr → Option Expr
  | .var _ => none
  | .lam _ _ => none
  | .app f a =>
      match f with
      | .lam x body => if valueB a then some (subst x a body) else none
      | _ => none
  | .bind x e₁ e₂ => if valueB e₁ then some (subst x e₁ e₂) else none
  | .matchC s c ys body =>
      match nodeTag? s with
      | some d =>
          if valueB s ∧ d = c ∧ ys.length = (nodeFields s).length then
            some (substAll ys (nodeFields s) body)
          else none
      | none => none
  | .dup _ _ => none
  | .drop _ _ => none
  | .con0 _ => none
  | .con1 _ _ => none
  | .con2 _ _ _ => none
  | .store s i v => if valueB s ∧ valueB v then slotUpdate s i v else none

/-- The leftmost-outermost step of a term, or `none` when it is stuck: the root
rules first, then a step in the function position of an application, in the
argument of an application whose function is a value, or in the bound term of a
binding. The recursion is structural on the term, so the kernel reduces the
evaluator at a concrete term. -/
def step? : Expr → Option Expr
  | .var x => rootStep? (.var x)
  | .lam x body => rootStep? (.lam x body)
  | .app f a =>
      match rootStep? (.app f a) with
      | some e' => some e'
      | none =>
          match step? f with
          | some f' => some (.app f' a)
          | none => if valueB f then (step? a).map (fun a' => .app f a') else none
  | .bind x e₁ e₂ =>
      match rootStep? (.bind x e₁ e₂) with
      | some e' => some e'
      | none => (step? e₁).map (fun e₁' => .bind x e₁' e₂)
  | .matchC s c ys body => rootStep? (.matchC s c ys body)
  | .dup x e => rootStep? (.dup x e)
  | .drop x e => rootStep? (.drop x e)
  | .con0 c => rootStep? (.con0 c)
  | .con1 c a => rootStep? (.con1 c a)
  | .con2 c a b => rootStep? (.con2 c a b)
  | .store s i v => rootStep? (.store s i v)

/-- The root part of the evaluator computes only redexes of `Root`. -/
theorem rootStep?_sound : ∀ {e e' : Expr}, rootStep? e = some e' → Root e e' := by
  intro e
  cases e with
  | var x => intro e' h; simp [rootStep?] at h
  | lam x body => intro e' h; simp [rootStep?] at h
  | app f a =>
      cases f with
      | var x => intro e' h; simp [rootStep?] at h
      | lam x body =>
          intro e' h
          by_cases hv : valueB a = true
          · simp [rootStep?, hv, Option.some.injEq] at h
            rw [← h]
            exact Root.beta ((valueB_iff a).mp hv)
          · simp [rootStep?, hv] at h
      | app g b => intro e' h; simp [rootStep?] at h
      | bind z e₁ e₂ => intro e' h; simp [rootStep?] at h
      | matchC s c ys b => intro e' h; simp [rootStep?] at h
      | dup z ez => intro e' h; simp [rootStep?] at h
      | drop z ez => intro e' h; simp [rootStep?] at h
      | con0 z => intro e' h; simp [rootStep?] at h
      | con1 z a' => intro e' h; simp [rootStep?] at h
      | con2 z a' b' => intro e' h; simp [rootStep?] at h
      | store z i' v' => intro e' h; simp [rootStep?] at h
  | bind x e₁ e₂ =>
      intro e' h
      by_cases hv : valueB e₁ = true
      · simp [rootStep?, hv, Option.some.injEq] at h
        rw [← h]
        exact Root.bindVal ((valueB_iff e₁).mp hv)
      · simp [rootStep?, hv] at h
  | matchC s c ys body =>
      intro e' h
      cases ht : nodeTag? s with
      | none => simp [rootStep?, ht] at h
      | some d =>
          by_cases hc : valueB s ∧ d = c ∧ ys.length = (nodeFields s).length
          · simp [rootStep?, ht, hc, Option.some.injEq] at h
            rw [← h]
            rw [hc.2.1] at ht
            exact Root.matchVal ((valueB_iff s).mp hc.1) ht hc.2.2
          · simp [rootStep?, ht, ite_eq_right hc] at h
  | dup x ex => intro e' h; simp [rootStep?] at h
  | drop x ex => intro e' h; simp [rootStep?] at h
  | con0 c => intro e' h; simp [rootStep?] at h
  | con1 c a => intro e' h; simp [rootStep?] at h
  | con2 c a b => intro e' h; simp [rootStep?] at h
  | store s i v =>
      intro e' h
      by_cases hc : valueB s ∧ valueB v
      · simp [rootStep?, hc] at h
        cases hsu : slotUpdate s i v with
        | none => rw [hsu] at h; simp at h
        | some n'' =>
            rw [hsu] at h
            simp [Option.some.injEq] at h
            rw [← h]
            exact Root.storeVal ((valueB_iff s).mp hc.1) ((valueB_iff v).mp hc.2) hsu
      · simp [rootStep?, ite_eq_right hc] at h

/-- The evaluator computes only steps of `Step`. The recursion is structural on
the term, which is what lets a `#guard` on the evaluator be a statement about
`Step`. -/
theorem step?_sound : ∀ (e : Expr) (e' : Expr), step? e = some e' → Step e e' := by
  intro e
  cases e with
  | var x =>
      intro e' h
      simp only [step?] at h
      exact Step.root (rootStep?_sound h)
  | lam x body =>
      intro e' h
      simp only [step?] at h
      exact Step.root (rootStep?_sound h)
  | app f a =>
      intro e' h
      cases hr : rootStep? (.app f a) with
      | some q =>
          simp only [step?, hr] at h
          cases h
          exact Step.root (rootStep?_sound hr)
      | none =>
          simp only [step?, hr] at h
          cases hf : step? f with
          | some q =>
              rw [hf] at h
              cases h
              exact Step.appFun (step?_sound f q hf)
          | none =>
              rw [hf] at h
              by_cases hv : valueB f
              · rw [ite_eq_left hv] at h
                cases ha : step? a with
                | none => rw [ha] at h; simp at h
                | some q =>
                    rw [ha] at h
                    simp only [Option.map_some, Option.some.injEq] at h
                    cases h
                    exact Step.appArg ((valueB_iff f).mp hv) (step?_sound a q ha)
              · rw [ite_eq_right hv] at h
                simp at h
  | bind x e₁ e₂ =>
      intro e' h
      cases hr : rootStep? (.bind x e₁ e₂) with
      | some q =>
          simp only [step?, hr] at h
          cases h
          exact Step.root (rootStep?_sound hr)
      | none =>
          simp only [step?, hr] at h
          cases hf : step? e₁ with
          | none => rw [hf] at h; simp at h
          | some q =>
              rw [hf] at h
              simp only [Option.map_some, Option.some.injEq] at h
              cases h
              exact Step.bindFun (step?_sound e₁ q hf)
  | matchC s c ys body =>
      intro e' h
      simp only [step?] at h
      exact Step.root (rootStep?_sound h)
  | dup x e =>
      intro e' h
      simp only [step?] at h
      exact Step.root (rootStep?_sound h)
  | drop x e =>
      intro e' h
      simp only [step?] at h
      exact Step.root (rootStep?_sound h)
  | con0 c =>
      intro e' h
      simp only [step?] at h
      exact Step.root (rootStep?_sound h)
  | con1 c a =>
      intro e' h
      simp only [step?] at h
      exact Step.root (rootStep?_sound h)
  | con2 c a b =>
      intro e' h
      simp only [step?] at h
      exact Step.root (rootStep?_sound h)
  | store s i v =>
      intro e' h
      simp only [step?] at h
      exact Step.root (rootStep?_sound h)

/-! ## Purity along an evaluation path

A term of the source fragment is reduced only by rules whose contracta are
subterms of the term and substitutions of bindings, and both stay pure: the
fragment has no resource operation on any path. -/

/-- The reflexive-transitive closure of the reduction: an evaluation path. -/
inductive StepStar : Expr → Expr → Prop where
  /-- A term evaluates to itself. -/
  | refl (e : Expr) : StepStar e e
  /-- One step and the rest of the path. -/
  | step {e e' e'' : Expr} : Step e e' → StepStar e' e'' → StepStar e e''

/-- The term a bounded evaluation reaches: `step?` repeated at most `fuel` times,
and the stuck term it stops at. The recursion is structural on the fuel, so the
kernel evaluates it at a concrete term. -/
def run : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e =>
      match step? e with
      | some e' => run fuel e'
      | none => e

/-- A bounded evaluation is a path of steps: the term `run` reaches is reached by
`StepStar`, so a guarded value is a fact about the reduction and not only about
the evaluator. -/
theorem run_stepStar : ∀ (fuel : Nat) (e : Expr), StepStar e (run fuel e)
  | 0, e => StepStar.refl e
  | fuel + 1, e => by
      rw [run]
      cases h : step? e with
      | none => exact StepStar.refl e
      | some e' => exact StepStar.step (step?_sound e e' h) (run_stepStar fuel e')

/-- A step of a pure term leaves a pure term: the source fragment is closed under
reduction. -/
theorem step_preserves_pure {e e' : Expr} (hs : Step e e') : Pure e → Pure e' := by
  induction hs with
  | root hr =>
      intro he
      cases hr with
      | beta hv =>
          obtain ⟨hlam, hv'⟩ := (pure_app_iff _ _).mp he
          exact subst_pure _ _ _ ((pure_lam_iff _ _).mp hlam) hv'
      | bindVal hv =>
          obtain ⟨hv', hbody⟩ := (pure_bind_iff _ _ _).mp he
          exact subst_pure _ _ _ hbody hv'
      | matchVal hs' ht hlen =>
          obtain ⟨hsubj, hbody⟩ := (pure_matchC_iff _ _ _ _).mp he
          exact substAll_pure _ _ hbody (nodeFields_pure hsubj)
      | storeVal hs' hv hsu =>
          obtain ⟨hsubj, hv'⟩ := (pure_store_iff _ _ _).mp he
          exact slotUpdate_pure hsubj hv' hsu
  | appFun hs ih =>
      intro he
      obtain ⟨hf, ha⟩ := (pure_app_iff _ _).mp he
      exact (pure_app_iff _ _).mpr ⟨ih hf, ha⟩
  | appArg hf hs ih =>
      intro he
      obtain ⟨hfun, ha⟩ := (pure_app_iff _ _).mp he
      exact (pure_app_iff _ _).mpr ⟨hfun, ih ha⟩
  | bindFun hs ih =>
      intro he
      obtain ⟨h₁, h₂⟩ := (pure_bind_iff _ _ _).mp he
      exact (pure_bind_iff _ _ _).mpr ⟨ih h₁, h₂⟩

/-- Along any evaluation path a pure term stays pure: no `dup` and no `drop`
appears, and the fragment is closed. -/
theorem pure_steps_pure {e e' : Expr} (hs : StepStar e e') : Pure e → Pure e' := by
  induction hs with
  | refl => intro he; exact he
  | step hstep _ ih =>
      intro he
      exact ih (step_preserves_pure hstep he)

end Scidonia.RC
