/-
The lowering from the source calculus λPure to the reference-counted target λRC:
the relation `Lower` of Reinking, Xie, de Moura and Leijen, *Perceus: Garbage
Free Reference Counting with Reuse* (PLDI 2021) Figures 5 and 8, the
syntax-directed strategy that realises it, and the two facts that make the
strategy a function of the environments: it is total on the source fragment, and
it answers at most one target.

The judgement is `Δ | Γ ⊢ e ⇝ e′`. `Δ` is the *borrowed* environment — the
occurrences the enclosing context owns and lends, which the term may use any
number of times at no cost, because the context keeps them. `Γ` is the *owned*
environment — the occurrences the term itself must consume, one per use. The
target carries two operations the source does not have, and the lowering is what
puts them there: `dup x; e` for a use the owned environment does not supply, and
`drop x; e` for an owned occurrence the term does not use. A source term writes
neither, which is what `Pure` in `Scidonia.RC.Syntax` says, so `Lower` has a rule
for every construct of the source and none for a `dup` or a `drop` node.

**The environments.** Both are lists of variable occurrences (`Occs`), read as
multisets: what matters is how many occurrences of a name a list holds, and the
list order is what makes the splits and the instruction order determinate, so
nothing here is claimed to be invariant under reordering. A count function
`Var → Nat` would say the same about multiplicities but has no computable support,
and the strategy has to walk the environment to place `dup` and `drop`; a list is
finite, which is what a strategy needs. The choice is what makes the splits
canonical, and canonical splits are what determinism needs: with an arbitrary
split of the environment between two subterms, two lowerings of one term from one
environment could place the same `dup` in different subterms and the targets
would differ, so `Lower`'s splits are written with the functions below rather
than by an existential.

**Where the instructions land.** Each rule's conclusion wraps the translated
subterm in the *prologue* of the differential between the environment it was
handed and the occurrences the term uses: a `dup x` for each use of an owned name
the environment does not supply, in the order the uses appear, and then a `drop
x` for each owned occurrence the term does not use, in the environment's order.
The subterms are translated under the occurrences the term's own usage claims
(`claimEnv`), and a binder hands its binding one owned occurrence of its name on
top of the occurrences the body's other names claim (`bindEnv`, `armEnv`) — so
the body of a binding whose name `e₂` uses twice is wrapped in a `dup x`, and the
body of a binding whose name `e₂` does not use is wrapped in a `drop x`. Those
are the two instructions of Figures 5 and 8 in their usual positions.

## What is proved

* `lowerB_sound` and `lowerB_complete`: the strategy's graph is the relation, so
  `Lower Δ Γ e e′` holds exactly when `lowerB Δ Γ e` answers `e′`.
* `lowerB_total`: the strategy answers for every term of the source fragment
  under every environment that fits it — which is why `Lower` is total.
* `lower_total`: every pure expression has a lowering from the environments that
  fit it (`Fits`: every variable the term uses is owned or borrowed somewhere).
* `lower_deterministic`: any two lowerings of one expression from the same
  borrowed and owned environments produce the same target.

## What is modelled, and what is not

A `var` rule's premise is that the variable is owned or borrowed; a variable in
neither is not lowered at all, which is the fit condition `Fits` states at the top
of a term. The strategy's recursion is structural on the term, so the kernel
evaluates it at a concrete term and the checks read it back with `#guard`.

Nothing here is claimed about the *meaning* of the target: that a target consumes
each of its occurrences exactly once, that the two operations it gained are the
ones a reference-counting runtime performs, and that its reduction preserves the
source's are properties of λRC, which this slice does not build. What is here is
the translation itself: which term a source term becomes under which environment,
and that the answer is unique.
-/

import Scidonia.RC.Pure

namespace Scidonia.RC

/-! ## Occurrence lists

An environment for the lowering is a multiset of variable occurrences written as
a list: what matters is how many occurrences of a name it holds. -/

/-- An environment for the lowering: the occurrences it holds, as a list read for
its multiplicities. -/
abbrev Occs := List Var

/-! ## Usage

The free occurrences of a variable in a term, as a list read for its
multiplicities. A binder removes its name's occurrences from its scope, which is
the shadowing `Scidonia.RC.Syntax` leaves in the syntax and
`Scidonia.RC.Pure`'s environment reads the same way. -/

/-- The free occurrences of a variable, as a multiset in list form. A binder's
name is removed from the whole of its scope, so a later binder of the same name
shadows an earlier one for the usage as well. A `dup` or a `drop` node uses its
name once besides the occurrences of its body; neither is source syntax, and the
usage is total on the syntax only because the recursion has to be. -/
def uses : Expr → List Var
  | .var x => [x]
  | .lam x body => (uses body).filter (fun y => y ≠ x)
  | .app f a => uses f ++ uses a
  | .bind x e₁ e₂ => uses e₁ ++ (uses e₂).filter (fun y => y ≠ x)
  | .matchC x _ ys body => x :: (uses body).filter (fun y => y ∉ ys)
  | .dup x e => x :: uses e
  | .drop x e => x :: uses e
  | .con0 _ => []
  | .con1 _ a => uses a
  | .con2 _ a b => uses a ++ uses b
  | .store x _ v => x :: uses v

/-! ## The environments a subterm is handed

The occurrences a term claims — its usage's occurrences whose name the
environment holds — and what a binder adds to the occurrences its body's other
names claim. -/

/-- The occurrences of an environment a usage claims: the usage's occurrences
whose name the environment holds. -/
def claimEnv (Γ : Occs) (u : List Var) : Occs := u.filter (fun y => y ∈ Γ)

/-- The occurrences a binding's body is handed: one owned occurrence of the
binder's name, beside the occurrences the body's other names claim. -/
def bindEnv (Γ : Occs) (x : Var) (u : List Var) : Occs :=
  [x] ++ u.filter (fun y => y ∈ Γ ∧ y ≠ x)

/-- The occurrences an arm's body is handed: one owned occurrence per binder,
beside the occurrences the body's other names claim. -/
def armEnv (Γ : Occs) (ys : List Var) (u : List Var) : Occs :=
  ys ++ u.filter (fun y => y ∈ Γ ∧ y ∉ ys)

/-- An environment with a name forgotten: a binder's name shadows the occurrences
the environment holds, owned and borrowed alike. -/
def forget (Δ : Occs) (x : Var) : Occs := Δ.filter (fun y => y ≠ x)

/-- An environment with the names of a list forgotten. -/
def forgetAll (Δ : Occs) (ys : List Var) : Occs := Δ.filter (fun y => y ∉ ys)

/-! ## The differential

The occurrences an environment claims and the uses it does not supply, and the
wrap that turns the difference into the two resource instructions. -/

/-- The occurrences of the environment a usage does not take, in the
environment's order: one `drop` per occurrence of this list releases them. -/
def surplus : Occs → List Var → Occs
  | [], _ => []
  | x :: xs, u => if x ∈ u then surplus xs (u.erase x) else x :: surplus xs u

/-- The uses an environment does not supply, in the order the uses appear: one
`dup` per occurrence of this list is what supplies them. -/
def deficit : Occs → List Var → List Var
  | _, [] => []
  | Γ, x :: xs => if x ∈ Γ then deficit (Γ.erase x) xs else x :: deficit Γ xs

/-- The target preceded by the instructions the differential demands: a `dup` for
each use the environment does not supply of a name it owns, in the order the uses
appear, and then a `drop` for each occurrence it does not take, in the
environment's order. -/
def wrap (Γ : Occs) (u : List Var) (e : Expr) : Expr :=
  ((deficit Γ u).filter (fun x => x ∈ Γ)).foldr (fun x e => .dup x e)
    ((surplus Γ u).foldr (fun x e => .drop x e) e)

/-- The environments that fit a term: every variable the term uses is owned or
borrowed. This is the hypothesis the totality theorem carries, and the condition
under which no variable of the term is left unbound by the lowering. -/
def Fits (Δ Γ : Occs) (e : Expr) : Prop := ∀ x ∈ uses e, x ∈ Γ ∨ x ∈ Δ

/-! ## The strategy

The syntax-directed lowering as a function: one equation per construct of the
syntax, the recursive calls under the occurrences the subterm's own usage claims,
and the binder cases handing their binding one owned occurrence of its name. A
`dup` or a `drop` node is not source syntax, so the strategy answers `none` at
one; the relation below has no rule for those either. -/

/-- The target the strategy gives a source term under a borrowed and an owned
environment, or `none` when a variable the term uses is neither. -/
def lowerB (Δ Γ : Occs) : Expr → Option Expr
  | .var x => if x ∈ Γ ∨ x ∈ Δ then some (wrap Γ [x] (.var x)) else none
  | .lam x body =>
      match lowerB (forget Δ x) (bindEnv Γ x (uses body)) body with
      | none => none
      | some body' => some (wrap Γ (uses (.lam x body)) (.lam x body'))
  | .app f a =>
      match lowerB Δ (claimEnv Γ (uses f)) f with
      | none => none
      | some f' =>
          match lowerB Δ (claimEnv Γ (uses a)) a with
          | none => none
          | some a' => some (wrap Γ (uses (.app f a)) (.app f' a'))
  | .bind x e₁ e₂ =>
      match lowerB Δ (claimEnv Γ (uses e₁)) e₁ with
      | none => none
      | some e₁' =>
          match lowerB (forget Δ x) (bindEnv Γ x (uses e₂)) e₂ with
          | none => none
          | some e₂' => some (wrap Γ (uses (.bind x e₁ e₂)) (.bind x e₁' e₂'))
  | .matchC x c ys body =>
      if x ∈ Γ ∨ x ∈ Δ then
        match lowerB (forgetAll Δ ys) (armEnv Γ ys (uses body)) body with
        | none => none
        | some body' => some (wrap Γ (uses (.matchC x c ys body)) (.matchC x c ys body'))
      else none
  | .dup _ _ => none
  | .drop _ _ => none
  | .con0 c => some (wrap Γ [] (.con0 c))
  | .con1 c a =>
      match lowerB Δ (claimEnv Γ (uses a)) a with
      | none => none
      | some a' => some (wrap Γ (uses (.con1 c a)) (.con1 c a'))
  | .con2 c a b =>
      match lowerB Δ (claimEnv Γ (uses a)) a with
      | none => none
      | some a' =>
          match lowerB Δ (claimEnv Γ (uses b)) b with
          | none => none
          | some b' => some (wrap Γ (uses (.con2 c a b)) (.con2 c a' b'))
  | .store x i v =>
      if x ∈ Γ ∨ x ∈ Δ then
        match lowerB Δ (claimEnv Γ (uses v)) v with
        | none => none
        | some v' => some (wrap Γ (uses (.store x i v)) (.store x i v'))
      else none

/-! ## The relation

`Δ | Γ ⊢ e ⇝ e′`, one rule per construct of the source, its splits written with
the functions above so that a rule's conclusion is the whole of what the relation
says about a construct. -/

/-- The lowering relation `Δ | Γ ⊢ e ⇝ e′`: the source term `e` lowers to the
target `e′` under the borrowed occurrences `Δ` and the owned occurrences `Γ`. -/
inductive Lower : Occs → Occs → Expr → Expr → Prop where
  /-- A variable an environment supplies lowers to itself; the prologue releases
  the owned occurrences of its name the use does not take. -/
  | var {Δ Γ x} (h : x ∈ Γ ∨ x ∈ Δ) : Lower Δ Γ (.var x) (wrap Γ [x] (.var x))
  /-- An abstraction lowers to an abstraction under the occurrences its body's
  other names claim, its name bound by the binder. -/
  | lam {Δ Γ x body body'} (h : Lower (forget Δ x) (bindEnv Γ x (uses body)) body body') :
      Lower Δ Γ (.lam x body) (wrap Γ (uses (.lam x body)) (.lam x body'))
  /-- An application lowers to an application, the environment split between the
  occurrences the term's usage claims for its two subterms. -/
  | app {Δ Γ f a f' a'} (hf : Lower Δ (claimEnv Γ (uses f)) f f')
      (ha : Lower Δ (claimEnv Γ (uses a)) a a') :
      Lower Δ Γ (.app f a) (wrap Γ (uses (.app f a)) (.app f' a'))
  /-- A binding lowers to a binding: its first term under the occurrences it
  claims, its second under those plus the one its name binds. -/
  | bind {Δ Γ x e₁ e₂ e₁' e₂'} (h₁ : Lower Δ (claimEnv Γ (uses e₁)) e₁ e₁')
      (h₂ : Lower (forget Δ x) (bindEnv Γ x (uses e₂)) e₂ e₂') :
      Lower Δ Γ (.bind x e₁ e₂) (wrap Γ (uses (.bind x e₁ e₂)) (.bind x e₁' e₂'))
  /-- A match lowers to a match whose arm binds the matched node's fields: one
  owned occurrence per binder, beside the occurrences the body's other names
  claim. -/
  | matchC {Δ Γ x c ys body body'} (hx : x ∈ Γ ∨ x ∈ Δ)
      (h : Lower (forgetAll Δ ys) (armEnv Γ ys (uses body)) body body') :
      Lower Δ Γ (.matchC x c ys body)
        (wrap Γ (uses (.matchC x c ys body)) (.matchC x c ys body'))
  /-- A nullary node lowers to itself. -/
  | con0 {Δ Γ c} : Lower Δ Γ (.con0 c) (wrap Γ [] (.con0 c))
  /-- A unary node lowers to a unary node whose field is lowered. -/
  | con1 {Δ Γ c a a'} (h : Lower Δ (claimEnv Γ (uses a)) a a') :
      Lower Δ Γ (.con1 c a) (wrap Γ (uses (.con1 c a)) (.con1 c a'))
  /-- A binary node lowers to a binary node whose two fields are lowered, the
  environment split between them. -/
  | con2 {Δ Γ c a b a' b'} (h₁ : Lower Δ (claimEnv Γ (uses a)) a a')
      (h₂ : Lower Δ (claimEnv Γ (uses b)) b b') :
      Lower Δ Γ (.con2 c a b) (wrap Γ (uses (.con2 c a b)) (.con2 c a' b'))
  /-- A write lowers to a write: its value is lowered, its target variable is the
  occurrence the prologue handles. -/
  | store {Δ Γ x i v v'} (hx : x ∈ Γ ∨ x ∈ Δ) (h : Lower Δ (claimEnv Γ (uses v)) v v') :
      Lower Δ Γ (.store x i v) (wrap Γ (uses (.store x i v)) (.store x i v'))

/-! ## The strategy is the relation -/

/-- A term the strategy answers is a term the relation lowers, to the very target
the strategy answered. -/
theorem lowerB_sound : ∀ (e : Expr) (Δ Γ : Occs) (e' : Expr),
    lowerB Δ Γ e = some e' → Lower Δ Γ e e'
  | .var x, Δ, Γ, e', h => by
      by_cases hx : x ∈ Γ ∨ x ∈ Δ
      · simp [lowerB, hx] at h
        rw [← h]
        exact Lower.var hx
      · simp [lowerB, hx] at h
  | .lam x body, Δ, Γ, e', h => by
      cases hb : lowerB (forget Δ x) (bindEnv Γ x (uses body)) body with
      | none => simp [lowerB, hb] at h
      | some body' =>
          simp [lowerB, hb] at h
          rw [← h]
          exact Lower.lam (lowerB_sound body _ _ body' hb)
  | .app f a, Δ, Γ, e', h => by
      cases hf : lowerB Δ (claimEnv Γ (uses f)) f with
      | none => simp [lowerB, hf] at h
      | some f' =>
          cases ha : lowerB Δ (claimEnv Γ (uses a)) a with
          | none => simp [lowerB, hf, ha] at h
          | some a' =>
              simp [lowerB, hf, ha] at h
              rw [← h]
              exact Lower.app (lowerB_sound f _ _ f' hf) (lowerB_sound a _ _ a' ha)
  | .bind x e₁ e₂, Δ, Γ, e', h => by
      cases h₁ : lowerB Δ (claimEnv Γ (uses e₁)) e₁ with
      | none => simp [lowerB, h₁] at h
      | some e₁' =>
          cases h₂ : lowerB (forget Δ x) (bindEnv Γ x (uses e₂)) e₂ with
          | none => simp [lowerB, h₁, h₂] at h
          | some e₂' =>
              simp [lowerB, h₁, h₂] at h
              rw [← h]
              exact Lower.bind (lowerB_sound e₁ _ _ e₁' h₁) (lowerB_sound e₂ _ _ e₂' h₂)
  | .matchC x c ys body, Δ, Γ, e', h => by
      by_cases hx : x ∈ Γ ∨ x ∈ Δ
      · simp only [lowerB, hx] at h
        cases hb : lowerB (forgetAll Δ ys) (armEnv Γ ys (uses body)) body with
        | none => simp [hb] at h
        | some body' =>
            simp [hb] at h
            rw [← h]
            exact Lower.matchC hx (lowerB_sound body _ _ body' hb)
      · simp [lowerB, hx] at h
  | .dup x ex, Δ, Γ, e', h => by simp [lowerB] at h
  | .drop x ex, Δ, Γ, e', h => by simp [lowerB] at h
  | .con0 c, Δ, Γ, e', h => by
      simp [lowerB] at h
      rw [← h]
      exact Lower.con0
  | .con1 c a, Δ, Γ, e', h => by
      cases ha : lowerB Δ (claimEnv Γ (uses a)) a with
      | none => simp [lowerB, ha] at h
      | some a' =>
          simp [lowerB, ha] at h
          rw [← h]
          exact Lower.con1 (lowerB_sound a _ _ a' ha)
  | .con2 c a b, Δ, Γ, e', h => by
      cases ha : lowerB Δ (claimEnv Γ (uses a)) a with
      | none => simp [lowerB, ha] at h
      | some a' =>
          cases hb : lowerB Δ (claimEnv Γ (uses b)) b with
          | none => simp [lowerB, ha, hb] at h
          | some b' =>
              simp [lowerB, ha, hb] at h
              rw [← h]
              exact Lower.con2 (lowerB_sound a _ _ a' ha) (lowerB_sound b _ _ b' hb)
  | .store x i v, Δ, Γ, e', h => by
      by_cases hx : x ∈ Γ ∨ x ∈ Δ
      · simp only [lowerB, hx] at h
        cases hv : lowerB Δ (claimEnv Γ (uses v)) v with
        | none => simp [hv] at h
        | some v' =>
            simp [hv] at h
            rw [← h]
            exact Lower.store hx (lowerB_sound v _ _ v' hv)
      · simp [lowerB, hx] at h

/-- A term the relation lowers is a term the strategy answers. -/
theorem lowerB_complete : ∀ {Δ Γ : Occs} {e e' : Expr}, Lower Δ Γ e e' →
    lowerB Δ Γ e = some e'
  | _, _, _, _, .var h => by
      simp [lowerB, h]
  | _, _, _, _, .lam h => by
      have hb := lowerB_complete h
      simp [lowerB, hb]
  | _, _, _, _, .app hf ha => by
      have h₁ := lowerB_complete hf
      have h₂ := lowerB_complete ha
      simp [lowerB, h₁, h₂]
  | _, _, _, _, .bind h₁ h₂ => by
      have hb₁ := lowerB_complete h₁
      have hb₂ := lowerB_complete h₂
      simp [lowerB, hb₁, hb₂]
  | _, _, _, _, .matchC hx h => by
      have hb := lowerB_complete h
      simp [lowerB, hx, hb]
  | _, _, _, _, .con0 => by
      simp [lowerB]
  | _, _, _, _, .con1 h => by
      have hb := lowerB_complete h
      simp [lowerB, hb]
  | _, _, _, _, .con2 h₁ h₂ => by
      have hb₁ := lowerB_complete h₁
      have hb₂ := lowerB_complete h₂
      simp [lowerB, hb₁, hb₂]
  | _, _, _, _, .store hx h => by
      have hb := lowerB_complete h
      simp [lowerB, hx, hb]

/-! ## Totality and determinism -/

/-- The strategy answers every term of the source fragment under every
environment that fits it: no variable the term uses is left unbound, and the
occurrences a variable is handed cover its uses. -/
theorem lowerB_total : ∀ (e : Expr), Pure e → ∀ (Δ Γ : Occs), Fits Δ Γ e →
    ∃ e', lowerB Δ Γ e = some e'
  | .var x, _, Δ, Γ, hfit => by
      have hx : x ∈ Γ ∨ x ∈ Δ := hfit x (by simp [uses])
      exact ⟨wrap Γ [x] (.var x), by simp [lowerB, hx]⟩
  | .lam x body, hp, Δ, Γ, hfit => by
      have hpbody : Pure body := (pure_lam_iff x body).mp hp
      have hfit' : Fits (forget Δ x) (bindEnv Γ x (uses body)) body := by
        intro y hy
        by_cases hyx : y = x
        · exact Or.inl (by simp [bindEnv, hyx])
        · have hy' : y ∈ uses (.lam x body) := by simp [uses, hy, hyx]
          rcases hfit y hy' with hyΓ | hyΔ
          · exact Or.inl (by simp [bindEnv, hy, hyΓ, hyx])
          · exact Or.inr (by simp [forget, hyΔ, hyx])
      obtain ⟨body', hb⟩ := lowerB_total body hpbody _ _ hfit'
      exact ⟨wrap Γ (uses (.lam x body)) (.lam x body'), by simp [lowerB, hb]⟩
  | .app f a, hp, Δ, Γ, hfit => by
      obtain ⟨hp₁, hp₂⟩ := (pure_app_iff f a).mp hp
      have hfit₁ : Fits Δ (claimEnv Γ (uses f)) f := by
        intro y hy
        rcases hfit y (by simp [uses, hy]) with hyΓ | hyΔ
        · exact Or.inl (by simp [claimEnv, hy, hyΓ])
        · exact Or.inr hyΔ
      have hfit₂ : Fits Δ (claimEnv Γ (uses a)) a := by
        intro y hy
        rcases hfit y (by simp [uses, hy]) with hyΓ | hyΔ
        · exact Or.inl (by simp [claimEnv, hy, hyΓ])
        · exact Or.inr hyΔ
      obtain ⟨f', hf⟩ := lowerB_total f hp₁ _ _ hfit₁
      obtain ⟨a', ha⟩ := lowerB_total a hp₂ _ _ hfit₂
      exact ⟨wrap Γ (uses (.app f a)) (.app f' a'), by simp [lowerB, hf, ha]⟩
  | .bind x e₁ e₂, hp, Δ, Γ, hfit => by
      obtain ⟨hp₁, hp₂⟩ := (pure_bind_iff x e₁ e₂).mp hp
      have hfit₁ : Fits Δ (claimEnv Γ (uses e₁)) e₁ := by
        intro y hy
        rcases hfit y (by simp [uses, hy]) with hyΓ | hyΔ
        · exact Or.inl (by simp [claimEnv, hy, hyΓ])
        · exact Or.inr hyΔ
      have hfit₂ : Fits (forget Δ x) (bindEnv Γ x (uses e₂)) e₂ := by
        intro y hy
        by_cases hyx : y = x
        · exact Or.inl (by simp [bindEnv, hyx])
        · have hy' : y ∈ uses (.bind x e₁ e₂) := by simp [uses, hy, hyx]
          rcases hfit y hy' with hyΓ | hyΔ
          · exact Or.inl (by simp [bindEnv, hy, hyΓ, hyx])
          · exact Or.inr (by simp [forget, hyΔ, hyx])
      obtain ⟨e₁', h₁⟩ := lowerB_total e₁ hp₁ _ _ hfit₁
      obtain ⟨e₂', h₂⟩ := lowerB_total e₂ hp₂ _ _ hfit₂
      exact ⟨wrap Γ (uses (.bind x e₁ e₂)) (.bind x e₁' e₂'), by simp [lowerB, h₁, h₂]⟩
  | .matchC x c ys body, hp, Δ, Γ, hfit => by
      have hpbody : Pure body := (pure_matchC_iff x c ys body).mp hp
      have hx : x ∈ Γ ∨ x ∈ Δ := hfit x (by simp [uses])
      have hfit' : Fits (forgetAll Δ ys) (armEnv Γ ys (uses body)) body := by
        intro y hy
        by_cases hyys : y ∈ ys
        · exact Or.inl (by simp [armEnv, hyys])
        · have hy' : y ∈ uses (.matchC x c ys body) := by simp [uses, hy, hyys]
          rcases hfit y hy' with hyΓ | hyΔ
          · exact Or.inl (by simp [armEnv, hy, hyΓ, hyys])
          · exact Or.inr (by simp [forgetAll, hyΔ, hyys])
      obtain ⟨body', hb⟩ := lowerB_total body hpbody _ _ hfit'
      exact ⟨wrap Γ (uses (.matchC x c ys body)) (.matchC x c ys body'),
        by simp [lowerB, hx, hb]⟩
  | .dup x ex, hp, _, _, _ => by exact absurd hp (not_pure_dup x ex)
  | .drop x ex, hp, _, _, _ => by exact absurd hp (not_pure_drop x ex)
  | .con0 c, _, Δ, Γ, _ => ⟨wrap Γ [] (.con0 c), by simp [lowerB]⟩
  | .con1 c a, hp, Δ, Γ, hfit => by
      have hpa : Pure a := (pure_con1_iff c a).mp hp
      have hfit₁ : Fits Δ (claimEnv Γ (uses a)) a := by
        intro y hy
        rcases hfit y (by simp [uses, hy]) with hyΓ | hyΔ
        · exact Or.inl (by simp [claimEnv, hy, hyΓ])
        · exact Or.inr hyΔ
      obtain ⟨a', ha⟩ := lowerB_total a hpa _ _ hfit₁
      exact ⟨wrap Γ (uses (.con1 c a)) (.con1 c a'), by simp [lowerB, ha]⟩
  | .con2 c a b, hp, Δ, Γ, hfit => by
      obtain ⟨hp₁, hp₂⟩ := (pure_con2_iff c a b).mp hp
      have hfit₁ : Fits Δ (claimEnv Γ (uses a)) a := by
        intro y hy
        rcases hfit y (by simp [uses, hy]) with hyΓ | hyΔ
        · exact Or.inl (by simp [claimEnv, hy, hyΓ])
        · exact Or.inr hyΔ
      have hfit₂ : Fits Δ (claimEnv Γ (uses b)) b := by
        intro y hy
        rcases hfit y (by simp [uses, hy]) with hyΓ | hyΔ
        · exact Or.inl (by simp [claimEnv, hy, hyΓ])
        · exact Or.inr hyΔ
      obtain ⟨a', ha⟩ := lowerB_total a hp₁ _ _ hfit₁
      obtain ⟨b', hb⟩ := lowerB_total b hp₂ _ _ hfit₂
      exact ⟨wrap Γ (uses (.con2 c a b)) (.con2 c a' b'), by simp [lowerB, ha, hb]⟩
  | .store x i v, hp, Δ, Γ, hfit => by
      have hpv : Pure v := (pure_store_iff x i v).mp hp
      have hx : x ∈ Γ ∨ x ∈ Δ := hfit x (by simp [uses])
      have hfit₁ : Fits Δ (claimEnv Γ (uses v)) v := by
        intro y hy
        rcases hfit y (by simp [uses, hy]) with hyΓ | hyΔ
        · exact Or.inl (by simp [claimEnv, hy, hyΓ])
        · exact Or.inr hyΔ
      obtain ⟨v', hv⟩ := lowerB_total v hpv _ _ hfit₁
      exact ⟨wrap Γ (uses (.store x i v)) (.store x i v'), by simp [lowerB, hx, hv]⟩

/-- Every pure expression has a lowering from the environments that fit it. -/
theorem lower_total {Δ Γ : Occs} {e : Expr} (hp : Pure e) (hfit : Fits Δ Γ e) :
    ∃ e', Lower Δ Γ e e' := by
  obtain ⟨e', he'⟩ := lowerB_total e hp Δ Γ hfit
  exact ⟨e', lowerB_sound e Δ Γ e' he'⟩

/-- Any two lowerings of one expression from the same borrowed and owned
environments produce the same target. -/
theorem lower_deterministic {Δ Γ : Occs} {e e₁ e₂ : Expr} (h₁ : Lower Δ Γ e e₁)
    (h₂ : Lower Δ Γ e e₂) : e₁ = e₂ := by
  have hb₁ := lowerB_complete h₁
  have hb₂ := lowerB_complete h₂
  rw [hb₁] at hb₂
  exact Option.some.inj hb₂

end Scidonia.RC
