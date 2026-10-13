/-
The model of the ownership-typed fragment: the observation denotation, the
environment, the one-cell invariant, the array-threading recursion, and the
correspondence between that recursion and the existing λPure reduction.

**Two semantics of one term.** The *copying* side is the existing
`Scidonia.RC.Step`/`StepStar`/`Value` of `Scidonia.RC.Pure`, with the functional
`slotUpdate` of its write — not a second evaluator. The *direct* side is
`runOn`, a structurally recursive interpreter of the admitted fragment that
threads one `Array Slot` and an observation environment and returns a quoted
λPure value. `runOn_simulate` relates them: for an admitted term, with the
environment agreeing with its context and the one-cell invariant holding, the
direct evaluation returns a value the copying reduction of the *same* term
reaches, and that value has the shape its type gives it.

**The denotation.** `Denote o v` says `v` is the quotation of an element of the
observation `o`: the unit, a natural, a quoted slot, or a quoted pair of two
quoted slots. A description outside the constructible fragment is not read by
any rule of the fragment and admits no value, which is why the fragment's
variable rule carries its description's membership. `denote_shape` reads the
three syntactic facts the theorems use off a denotation: the value is a λPure
value, it is closed, and it carries no unary root node.

**The environment.** `VEnv` maps names to λPure values, a name being either
absent or holding one value. `inst ρ e` is the *instance* of `e` under `ρ`: its
free variables are replaced by their values, and that is the term the copying
reduction works on. `WF Γ ρ` is the agreement between the two: `Γ` and `ρ` have
exactly the same domain, every value of `ρ` is a closed λPure value, and a name
of an observation type holds a denotation of that description. A binder the
context is extended with extends the environment by its value, and the
substitution the copying reduction performs is exactly that extension:
`subst_inst` says `subst y v (inst ρ e) = inst (ρ.extend y v) e` for a name the
term does not bind, which is the capture freedom `own_no_rebind` supplies.

**The one-cell invariant.** `Inv κ a ρ` says that when a name holds the
protected cell, that name's value is the quoted root of exactly the slot the
array holds, and the array is the one-element array of that slot. The root
construction is the only rule that creates a cell and its admission is only from
the absent owner, and the hand-off names the fresh handle from the cell its
bound term yielded, so the invariant is re-established exactly where the rules
move the handle.

**The recursion.** `runWith` is the fragment's evaluation with the update step as
a parameter: a variable reads the environment, the constructors build their
node, a `rootTag` construction asks for exactly one fresh cell built from the
slot its operand denotes, a read borrows the array's element and binds its
quotation to the continuation's name, a write replaces the array's element with
the slot the written operand denotes and yields the quoted root of it, and a
binding extends the environment with the value it bound. `runOn` is that
recursion at `Array.set!`; a term outside the fragment is not evaluated and
yields `none`, and a write whose array holds no cell fails the same way rather
than returning a value built from the array it was given.
-/
import Scidonia.RC.OwnershipTyped.Judgement

namespace Scidonia.RC

namespace OwnershipTyped

open Scidonia.FracPerm.StateVar (Slot)
open Scidonia.FracPerm.StateVar.Layout5 (ObsDesc)

/-! ## The observation denotation -/

/-- The quotation of an element of the observation `o`: the unit, a natural, the
quotation of a slot, or the quotation of a pair of two slots. A description
outside the constructible fragment is read by no rule of the fragment and
admits no value. -/
def Denote : (o : ObsDesc) → Expr → Prop
  | .unit, v => v = quoteUnit
  | .nat, v => ∃ n, v = quoteNat n
  | .sum .unit .nat, v => ∃ s, v = quoteSlot s
  | .pair (.sum .unit .nat) (.sum .unit .nat), v =>
      ∃ s t, v = quotePair (quoteSlot s) (quoteSlot t)
  | _, _ => False

/-- A value the unit denotation admits is a λPure value, is closed, and carries
no unary root node. -/
theorem denote_shape_unit {v : Expr} (h : Denote .unit v) :
    Value v ∧ Closed v ∧ hasRoot v = false := by
  have hv : v = quoteUnit := h
  subst hv
  exact ⟨quoteUnit_value, quoteUnit_closed, no_root_quoteUnit⟩

/-- A value the natural denotation admits is a λPure value, is closed, and
carries no unary root node. -/
theorem denote_shape_nat {v : Expr} (h : Denote .nat v) :
    Value v ∧ Closed v ∧ hasRoot v = false := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨quoteNat_value n, quoteNat_closed n, no_root_quoteNat n⟩

/-- A value the slot denotation admits is a λPure value, is closed, and carries
no unary root node. -/
theorem denote_shape_slot {v : Expr} (h : Denote slotObs v) :
    Value v ∧ Closed v ∧ hasRoot v = false := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨quoteSlot_value s, quoteSlot_closed s, no_root_quoteSlot s⟩

/-- A value the pair denotation admits is a λPure value, is closed, and carries
no unary root node. -/
theorem denote_shape_pair {v : Expr} (h : Denote (.pair slotObs slotObs) v) :
    Value v ∧ Closed v ∧ hasRoot v = false := by
  obtain ⟨s, t, rfl⟩ := h
  exact ⟨quotePair_value (quoteSlot_value s) (quoteSlot_value t),
    quotePair_closed (quoteSlot_closed s) (quoteSlot_closed t),
    no_root_quotePair (no_root_quoteSlot s) (no_root_quoteSlot t)⟩

/-- A value a denotation of the constructible fragment admits is a λPure value,
is closed, and carries no unary root node: the three syntactic facts the
theorems read off a denotation. -/
theorem denote_shape {o : ObsDesc} {v : Expr} (hf : Fragment o) (h : Denote o v) :
    Value v ∧ Closed v ∧ hasRoot v = false := by
  cases hf with
  | unit => exact denote_shape_unit h
  | nat => exact denote_shape_nat h
  | slot => exact denote_shape_slot h
  | pair _ _ => exact denote_shape_pair h

/-! ## The observation environment -/

/-- An observation environment: the λPure value each name holds, or nothing. A
name is either absent or holds one value. -/
abbrev VEnv := Var → Option Expr

namespace VEnv

/-- The environment with `y` bound to `v`, shadowing any value `y` held. -/
def extend (ρ : VEnv) (y : Var) (v : Expr) : VEnv := fun z => if z = y then some v else ρ z

/-- The extended environment holds the bound name. -/
@[simp] theorem extend_self (ρ : VEnv) (y : Var) (v : Expr) : (extend ρ y v) y = some v := by
  simp [extend]

/-- The extended environment leaves every other name as the environment had it. -/
theorem extend_of_ne {ρ : VEnv} {y z : Var} {v : Expr} (h : z ≠ y) :
    (extend ρ y v) z = ρ z := by
  simp [extend, h]

end VEnv

/-- The instance of a term under an environment: every free variable is replaced
by the value the environment holds for it, and a variable the environment does
not hold is left alone. The term the copying reduction works on is this one. -/
def inst (ρ : VEnv) : Expr → Expr
  | .var x => (ρ x).getD (.var x)
  | .lam x body => .lam x (inst ρ body)
  | .app f a => .app (inst ρ f) (inst ρ a)
  | .bind x e₁ e₂ => .bind x (inst ρ e₁) (inst ρ e₂)
  | .matchC s c ys body => .matchC (inst ρ s) c ys (inst ρ body)
  | .dup x e => .dup x (inst ρ e)
  | .drop x e => .drop x (inst ρ e)
  | .con0 c => .con0 c
  | .con1 c a => .con1 c (inst ρ a)
  | .con2 c a b => .con2 c (inst ρ a) (inst ρ b)
  | .store s i v => .store (inst ρ s) i (inst ρ v)

/-- The instance of a term under the everywhere-absent environment is the term
itself. -/
theorem inst_none : ∀ e : Expr, inst (fun _ => none) e = e
  | .var x => rfl
  | .lam x body => by rw [inst, inst_none body]
  | .app f a => by rw [inst, inst_none f, inst_none a]
  | .bind x e₁ e₂ => by rw [inst, inst_none e₁, inst_none e₂]
  | .matchC s c ys body => by rw [inst, inst_none s, inst_none body]
  | .dup x e => by rw [inst, inst_none e]
  | .drop x e => by rw [inst, inst_none e]
  | .con0 c => rfl
  | .con1 c a => by rw [inst, inst_none a]
  | .con2 c a b => by rw [inst, inst_none a, inst_none b]
  | .store s i v => by rw [inst, inst_none s, inst_none v]

/-! ## Substitution and the environment extension -/

/-- Free occurrences of an abstraction's name: a name is free in `λx. body`
exactly when it is free in the body and is not `x`. -/
theorem mem_uses_lam {x y : Var} {body : Expr} :
    x ∈ uses (.lam y body) ↔ x ∈ uses body ∧ x ≠ y := by
  simp [uses, List.mem_filter]

/-- Free occurrences of a binding: a name is free in `val x = e₁; e₂` exactly
when it is free in `e₁` or in `e₂` without being `x`. -/
theorem mem_uses_bind {x y : Var} {e₁ e₂ : Expr} :
    x ∈ uses (.bind y e₁ e₂) ↔ x ∈ uses e₁ ∨ (x ∈ uses e₂ ∧ x ≠ y) := by
  simp [uses, List.mem_filter, List.mem_append]

/-- Free occurrences of a match: a name is free in `match s { c ȳ → body }`
exactly when it is free in the subject or in the arm's body outside the arm's
binders. -/
theorem mem_uses_matchC {x : Var} {s body : Expr} {c : Ctor} {ys : List Var} :
    x ∈ uses (.matchC s c ys body) ↔ x ∈ uses s ∨ (x ∈ uses body ∧ x ∉ ys) := by
  simp [uses, List.mem_filter, List.mem_append]

/-- A substitution for a name the term does not mention free changes nothing. -/
theorem subst_of_notMem : ∀ (e : Expr) (x : Var) (v : Expr), x ∉ uses e → subst x v e = e
  | .var y, x, v, h => by
      have hyx : y ≠ x := Ne.symm (by simpa [uses] using h)
      rw [subst, ite_eq_right hyx]
  | .lam y body, x, v, h => by
      rw [subst]
      by_cases hyx : y = x
      · rw [ite_eq_left hyx]
      · rw [ite_eq_right hyx]
        have hb : x ∉ uses body := fun hc => h (mem_uses_lam.mpr ⟨hc, fun hxy => hyx hxy.symm⟩)
        rw [subst_of_notMem body x v hb]
  | .app f a, x, v, h => by
      have hf : x ∉ uses f := fun hc => h (by simp [uses, hc])
      have ha : x ∉ uses a := fun hc => h (by simp [uses, hc])
      rw [subst, subst_of_notMem f x v hf, subst_of_notMem a x v ha]
  | .bind y e₁ e₂, x, v, h => by
      rw [subst]
      have h₁ : x ∉ uses e₁ := fun hc => h (mem_uses_bind.mpr (Or.inl hc))
      rw [subst_of_notMem e₁ x v h₁]
      by_cases hyx : y = x
      · rw [ite_eq_left hyx]
      · rw [ite_eq_right hyx]
        have h₂ : x ∉ uses e₂ :=
          fun hc => h (mem_uses_bind.mpr (Or.inr ⟨hc, fun hxy => hyx hxy.symm⟩))
        rw [subst_of_notMem e₂ x v h₂]
  | .matchC s c ys body, x, v, h => by
      rw [subst]
      have hs : x ∉ uses s := fun hc => h (mem_uses_matchC.mpr (Or.inl hc))
      rw [subst_of_notMem s x v hs]
      by_cases hx : x ∈ ys
      · rw [ite_eq_left hx]
      · rw [ite_eq_right hx]
        have hb : x ∉ uses body := fun hc => h (mem_uses_matchC.mpr (Or.inr ⟨hc, hx⟩))
        rw [subst_of_notMem body x v hb]
  | .dup y e, x, v, h => by
      have he : x ∉ uses e := fun hc => h (by simp [uses, hc])
      rw [subst, subst_of_notMem e x v he]
  | .drop y e, x, v, h => by
      have he : x ∉ uses e := fun hc => h (by simp [uses, hc])
      rw [subst, subst_of_notMem e x v he]
  | .con0 c, x, v, h => rfl
  | .con1 c a, x, v, h => by
      have ha : x ∉ uses a := by simpa [uses] using h
      rw [subst, subst_of_notMem a x v ha]
  | .con2 c a b, x, v, h => by
      have ha : x ∉ uses a := fun hc => h (by simp [uses, hc])
      have hb : x ∉ uses b := fun hc => h (by simp [uses, hc])
      rw [subst, subst_of_notMem a x v ha, subst_of_notMem b x v hb]
  | .store s i w, x, v, h => by
      have hs : x ∉ uses s := fun hc => h (by simp [uses, hc])
      have hw : x ∉ uses w := fun hc => h (by simp [uses, hc])
      rw [subst, subst_of_notMem s x v hs, subst_of_notMem w x v hw]

/-- A closed term is fixed by any substitution: it has no free occurrence of the
substituted name. -/
theorem subst_closed (e : Expr) (x : Var) (v : Expr) (h : Closed e) : subst x v e = e :=
  subst_of_notMem e x v (by rw [Closed] at h; rw [h]; simp)

/-- Substituting a name the term does not bind into its instance is extending the
environment with the substituted value: the copying reduction's substitution and
the interpreter's environment extension are the same step. -/
theorem subst_inst {ρ : VEnv} {y : Var} {v : Expr}
    (hy : ρ y = none) (hc : Closed v) (hρ : ∀ x w, ρ x = some w → Closed w) :
    ∀ (e : Expr), y ∉ binders e → subst y v (inst ρ e) = inst (VEnv.extend ρ y v) e
  | .var x, hb => by
      by_cases hxy : x = y
      · rw [hxy]
        simp only [inst, hy, VEnv.extend_self, Option.getD_none, Option.getD_some,
          subst_var_self]
      · have hxy' : x ≠ y := hxy
        by_cases hnone : ρ x = none
        · have hL : inst ρ (.var x) = .var x := by simp only [inst, hnone, Option.getD_none]
          have hR : inst (VEnv.extend ρ y v) (.var x) = .var x := by
            simp only [inst, VEnv.extend_of_ne hxy', hnone, Option.getD_none]
          rw [hL, hR, subst_var_of_ne hxy']
        · obtain ⟨w, hw⟩ : ∃ w, ρ x = some w := by
            cases hx : ρ x with
            | none => exact absurd hx hnone
            | some w => exact ⟨w, rfl⟩
          have hL : inst ρ (.var x) = w := by simp only [inst, hw, Option.getD_some]
          have hR : inst (VEnv.extend ρ y v) (.var x) = w := by
            simp only [inst, VEnv.extend_of_ne hxy', hw, Option.getD_some]
          rw [hL, hR, subst_closed w y v (hρ x w hw)]
  | .lam x body, hb => by
      have hxy : x ≠ y := fun h => hb (mem_binders_lam.mpr (Or.inl h.symm))
      have hb' : y ∉ binders body := fun h => hb (mem_binders_lam.mpr (Or.inr h))
      rw [inst, inst, subst, ite_eq_right hxy, subst_inst hy hc hρ body hb']
  | .app f a, hb => by
      have hf : y ∉ binders f := fun h => hb (by simp [binders, h])
      have ha : y ∉ binders a := fun h => hb (by simp [binders, h])
      rw [inst, inst, subst, subst_inst hy hc hρ f hf, subst_inst hy hc hρ a ha]
  | .bind x e₁ e₂, hb => by
      have hxy : x ≠ y := fun h => hb (mem_binders_bind.mpr (Or.inl h.symm))
      have h₁ : y ∉ binders e₁ := fun h => hb (mem_binders_bind.mpr (Or.inr (Or.inl h)))
      have h₂ : y ∉ binders e₂ := fun h => hb (mem_binders_bind.mpr (Or.inr (Or.inr h)))
      rw [inst, inst, subst, subst_inst hy hc hρ e₁ h₁, ite_eq_right hxy,
        subst_inst hy hc hρ e₂ h₂]
  | .matchC s c ys body, hb => by
      have hs : y ∉ binders s := fun h => hb (mem_binders_matchC.mpr (Or.inl h))
      have hys : y ∉ ys := fun h => hb (mem_binders_matchC.mpr (Or.inr (Or.inl h)))
      have hb' : y ∉ binders body := fun h => hb (mem_binders_matchC.mpr (Or.inr (Or.inr h)))
      rw [inst, inst, subst, subst_inst hy hc hρ s hs, ite_eq_right (by simpa using hys),
        subst_inst hy hc hρ body hb']
  | .dup x e, hb => by
      rw [inst, inst, subst, subst_inst hy hc hρ e hb]
  | .drop x e, hb => by
      rw [inst, inst, subst, subst_inst hy hc hρ e hb]
  | .con0 c, _ => rfl
  | .con1 c a, hb => by
      have ha : y ∉ binders a := fun h => hb (by simp [binders, h])
      rw [inst, inst, subst, subst_inst hy hc hρ a ha]
  | .con2 c a b, hb => by
      have ha : y ∉ binders a := fun h => hb (by simp [binders, h])
      have hb' : y ∉ binders b := fun h => hb (by simp [binders, h])
      rw [inst, inst, subst, subst_inst hy hc hρ a ha, subst_inst hy hc hρ b hb']
  | .store s i w, hb => by
      have hs : y ∉ binders s := fun h => hb (by simp [binders, h])
      have hw : y ∉ binders w := fun h => hb (by simp [binders, h])
      rw [inst, inst, subst, subst_inst hy hc hρ s hs, subst_inst hy hc hρ w hw]

/-! ## The agreement between the context and the environment -/

/-- The context and the environment agree: they have exactly the same domain,
every value the environment holds is a closed λPure value, and a name of an
observation type holds a denotation of that description. The observation types
of an admitted context are of the constructible fragment, which is the condition
the fragment's variable rule carries, so the third clause is satisfiable exactly
where the rules can produce an observation. -/
def WF (Γ : TyEnv) (ρ : VEnv) : Prop :=
  (∀ x, Γ x = none ↔ ρ x = none)
  ∧ (∀ x w, ρ x = some w → Value w ∧ Closed w)
  ∧ (∀ x o w, Γ x = some (.obs o) → ρ x = some w → Denote o w)

/-- A name the environment holds a value for is a name the context holds. -/
theorem WF.exists_of_some {Γ : TyEnv} {ρ : VEnv} (h : WF Γ ρ) {x : Var} {τ : Ty}
    (hx : Γ x = some τ) : ∃ w, ρ x = some w := by
  have hne : ρ x ≠ none := fun h' => by
    have hg : Γ x = none := (h.1 x).mpr h'
    rw [hx] at hg
    exact absurd hg (by simp)
  exact Option.ne_none_iff_exists'.mp hne

/-- The empty context agrees with the everywhere-absent environment. -/
theorem WF.empty : WF (TyEnv.empty : TyEnv) (fun _ => none) := by
  refine ⟨fun x => by simp [TyEnv.empty], ?_, ?_⟩
  · intro x w h
    exact absurd h (by simp)
  · intro x o w h
    exact absurd h (by simp)

/-- Binding a name to a denotation extends the agreement. -/
theorem WF.extend_obs {Γ : TyEnv} {ρ : VEnv} {y : Var} {o : ObsDesc} {v : Expr}
    (h : WF Γ ρ) (hf : Fragment o) (hv : Denote o v) :
    WF (Γ.extend y (.obs o)) (ρ.extend y v) := by
  obtain ⟨hv1, hv2, _⟩ := denote_shape hf hv
  obtain ⟨hd, hval, hden⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x
    by_cases hxy : x = y
    · rw [hxy, TyEnv.extend_self, VEnv.extend_self]
      simp
    · rw [TyEnv.extend_of_ne hxy, VEnv.extend_of_ne hxy]
      exact hd x
  · intro x w hxw
    by_cases hxy : x = y
    · have hwv : w = v := by
        rw [hxy, VEnv.extend_self] at hxw
        exact (Option.some.inj hxw).symm
      rw [hwv]
      exact ⟨hv1, hv2⟩
    · exact hval x w ((VEnv.extend_of_ne hxy).symm.trans hxw)
  · intro x o' w hx hxw
    by_cases hxy : x = y
    · rw [hxy, TyEnv.extend_self] at hx
      have hoo : o' = o := by
        injection hx with hoo
        cases hoo
        rfl
      rw [hoo]
      have hwv : w = v := by
        rw [hxy, VEnv.extend_self] at hxw
        exact (Option.some.inj hxw).symm
      rw [hwv]
      exact hv
    · rw [TyEnv.extend_of_ne hxy] at hx
      exact hden x o' w hx ((VEnv.extend_of_ne hxy).symm.trans hxw)

/-- Binding a name to a cell extends the agreement: a cell name carries no
observation type, so only the domain and the closed values have to survive. -/
theorem WF.extend_cell {Γ : TyEnv} {ρ : VEnv} {y : Var} {v : Expr}
    (h : WF Γ ρ) (hv1 : Value v) (hv2 : Closed v) :
    WF (Γ.extend y .cell) (ρ.extend y v) := by
  obtain ⟨hd, hval, hden⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x
    by_cases hxy : x = y
    · rw [hxy, TyEnv.extend_self, VEnv.extend_self]
      simp
    · rw [TyEnv.extend_of_ne hxy, VEnv.extend_of_ne hxy]
      exact hd x
  · intro x w hxw
    by_cases hxy : x = y
    · have hwv : w = v := by
        rw [hxy, VEnv.extend_self] at hxw
        exact (Option.some.inj hxw).symm
      rw [hwv]
      exact ⟨hv1, hv2⟩
    · exact hval x w ((VEnv.extend_of_ne hxy).symm.trans hxw)
  · intro x o' w hx hxw
    by_cases hxy : x = y
    · rw [hxy, TyEnv.extend_self] at hx
      exact absurd (Option.some.inj hx) (by simp)
    · rw [TyEnv.extend_of_ne hxy] at hx
      exact hden x o' w hx ((VEnv.extend_of_ne hxy).symm.trans hxw)

/-! ## The one-cell invariant -/

/-- The protected cell's invariant: when a name holds the cell and the context
types it as a cell, the value the environment holds for that name is the quoted
root of exactly the slot the array holds, and the array is the one-element array
of that slot. At no owner — before the root construction, or after the session's
cell has been discarded — the invariant says nothing. The context is a parameter
because a binding of an *observation* extends the environment without touching
the cell, and the invariant has to survive that: a name the context still types
as a cell is one the binding did not name. -/
def Inv (Γ : TyEnv) (κ : Owner) (a : Array Slot) (ρ : VEnv) : Prop :=
  ∀ x, κ = .held x → Γ x = some .cell → ∃ s, ρ x = some (root s) ∧ a = #[s]

/-- No owner holds a cell, so the invariant holds of any array and
environment. -/
theorem Inv.none {Γ : TyEnv} {a : Array Slot} {ρ : VEnv} : Inv Γ .none a ρ := by
  intro x h _
  exact absurd h (Owner.none_ne_held x)

/-- An observation binding extends the environment without touching the cell:
the invariant survives, because a name the extended context still types as a
cell is one the binding did not name. -/
theorem Inv.extend_obs {Γ : TyEnv} {κ : Owner} {a : Array Slot} {ρ : VEnv} {y : Var}
    {o : ObsDesc} {v : Expr} (h : Inv Γ κ a ρ) :
    Inv (Γ.extend y (.obs o)) κ a (VEnv.extend ρ y v) := by
  intro z hz hcell
  have hzy : z ≠ y := fun he => by
    rw [he, TyEnv.extend_self] at hcell
    exact absurd hcell (by simp)
  rw [TyEnv.extend_of_ne hzy] at hcell
  obtain ⟨s, hs, ha⟩ := h z hz hcell
  exact ⟨s, by rw [VEnv.extend_of_ne hzy]; exact hs, ha⟩

/-- A cell binding re-establishes the invariant for the continuation's fresh
name, from the cell the bound term yielded: the fresh name's value is the quoted
root of exactly the slot the array holds. -/
theorem Inv.extend_cell {Γ : TyEnv} {ρ : VEnv} {y : Var} {s : Slot} :
    Inv (Γ.extend y .cell) (.held y) #[s] (VEnv.extend ρ y (root s)) := by
  intro z hz _
  have hzy : z = y := (Owner.held_inj hz.symm)
  rw [hzy]
  exact ⟨s, VEnv.extend_self ρ y (root s), rfl⟩

/-! ## The array-threading recursion -/

/-- A borrowed read of the cell's single element. -/
def readCell (a : @& Array Slot) : Option Slot := a[0]?

/-- Writing slot `0` into the one-element array of a slot is the one-element
array of the written slot: the write's cell shape. -/
theorem set_singleton (s t : Slot) : (#[s] : Array Slot).set! 0 t = #[t] := by
  simp

/-- A borrowed read of the one-element array of a slot yields that slot. -/
theorem readCell_singleton (s : Slot) : readCell (#[s] : Array Slot) = some s := by
  simp [readCell]

/-- The evaluation of the fragment, with the update step as a parameter: the
sealed executor's own write goes through the exclusivity check and the model's
through `Array.set!`, and the recursion is the same one. A term outside the
fragment is not evaluated and yields `none`. A write is asked for only when the
array actually holds slot `0`: the guard is what keeps `Array.set!` off an empty
array, and a write threaded no cell fails the recursion instead of yielding a
value built from the array it was given. -/
def runWith (write : Array Slot → Slot → Array Slot) (ρ : VEnv) (a : Array Slot) :
    Expr → Option (Expr × Array Slot)
  | .var x => (ρ x).map (fun v => (v, a))
  | .con0 c => some (.con0 c, a)
  | .con1 c b =>
      (runWith write ρ a b).bind (fun p =>
        if c = rootTag then (unquoteSlot p.1).map (fun s => (.con1 rootTag p.1, #[s]))
        else some (.con1 c p.1, p.2))
  | .con2 c f s =>
      (runWith write ρ a f).bind (fun p =>
        (runWith write ρ p.2 s).map (fun q => (.con2 c p.1 q.1, q.2)))
  | .matchC s c ys body =>
      match s with
      | .var _ =>
          if c = rootTag then
            match ys with
            | [y] => (readCell a).bind (fun s' =>
                runWith write (VEnv.extend ρ y (quoteSlot s')) a body)
            | _ => none
          else none
      | _ => none
  | .store s i b =>
      match s with
      | .var _ =>
          if i = 0 then
            (runWith write ρ a b).bind (fun p =>
              if 0 < p.2.size then
                (unquoteSlot p.1).map (fun t => (.con1 rootTag p.1, write p.2 t))
              else none)
          else none
      | _ => none
  | .bind y e₁ e₂ =>
      (runWith write ρ a e₁).bind (fun p => runWith write (VEnv.extend ρ y p.1) p.2 e₂)
  | _ => none

/-- The fragment's evaluation with `Array.set!` as its update: the model's
denotation of an admitted term on an array the caller supplies. -/
abbrev runOn (ρ : VEnv) (a : Array Slot) (e : Expr) : Option (Expr × Array Slot) :=
  runWith (fun a t => a.set! 0 t) ρ a e

/-- Two update steps that agree everywhere give the same evaluation. -/
theorem runWith_congr {w₁ w₂ : Array Slot → Slot → Array Slot}
    (h : ∀ a t, w₁ a t = w₂ a t) :
    ∀ (e : Expr) (ρ : VEnv) (a : Array Slot), runWith w₁ ρ a e = runWith w₂ ρ a e := by
  intro e
  induction e with
  | var x => intro ρ a; rfl
  | con0 c => intro ρ a; rfl
  | con1 c b ih =>
      intro ρ a
      simp only [runWith]
      rw [ih ρ a]
  | con2 c f s ihf ihs =>
      intro ρ a
      simp only [runWith]
      rw [ihf ρ a]
      cases hv : runWith w₂ ρ a f with
      | none => rfl
      | some p =>
          show (runWith w₁ ρ p.2 s).map (fun q => (Expr.con2 c p.1 q.1, q.2)) =
            (runWith w₂ ρ p.2 s).map (fun q => (Expr.con2 c p.1 q.1, q.2))
          rw [ihs ρ p.2]
  | matchC s c ys body ihs ihb =>
      intro ρ a
      cases s with
      | var x =>
          simp only [runWith]
          cases ys with
          | nil => rfl
          | cons y t =>
              cases t with
              | nil =>
                  cases hv : readCell a with
                  | none => rfl
                  | some s' =>
                      show (if c = rootTag then
                          runWith w₁ (VEnv.extend ρ y (quoteSlot s')) a body
                        else none) =
                        (if c = rootTag then
                          runWith w₂ (VEnv.extend ρ y (quoteSlot s')) a body
                        else none)
                      rw [ihb (VEnv.extend ρ y (quoteSlot s')) a]
              | cons y' t' => rfl
      | lam x b => rfl
      | app f s' => rfl
      | bind x e₁ e₂ => rfl
      | dup x e => rfl
      | drop x e => rfl
      | con0 c' => rfl
      | con1 c' a' => rfl
      | con2 c' a' b' => rfl
      | store s' i b => rfl
      | matchC s' c' ys' body' => rfl
  | store s i b ihs ihb =>
      intro ρ a
      cases s with
      | var x =>
          simp only [runWith]
          rw [ihb ρ a]
          cases hv : runWith w₂ ρ a b with
          | none => rfl
          | some p =>
              show (if i = 0 then
                  (if 0 < p.2.size then
                    (unquoteSlot p.1).map (fun t => (Expr.con1 rootTag p.1, w₁ p.2 t))
                   else none)
                else none) =
                (if i = 0 then
                  (if 0 < p.2.size then
                    (unquoteSlot p.1).map (fun t => (Expr.con1 rootTag p.1, w₂ p.2 t))
                   else none)
                else none)
              rw [show w₁ p.2 = w₂ p.2 from funext (h p.2)]
      | lam x b => rfl
      | app f s' => rfl
      | bind x e₁ e₂ => rfl
      | dup x e => rfl
      | drop x e => rfl
      | con0 c' => rfl
      | con1 c' a' => rfl
      | con2 c' a' b' => rfl
      | matchC s' c ys body => rfl
      | store s' i' b' => rfl
  | bind y e₁ e₂ ih₁ ih₂ =>
      intro ρ a
      simp only [runWith]
      rw [ih₁ ρ a]
      cases hv : runWith w₂ ρ a e₁ with
      | none => rfl
      | some p =>
          show runWith w₁ (VEnv.extend ρ y p.1) p.2 e₂ =
            runWith w₂ (VEnv.extend ρ y p.1) p.2 e₂
          rw [ih₂ (VEnv.extend ρ y p.1) p.2]
  | lam x body => intro ρ a; rfl
  | app f s => intro ρ a; rfl
  | dup x e => intro ρ a; rfl
  | drop x e => intro ρ a; rfl

/-- The evaluation of an observation returns exactly the instance of the
observation and never touches the array: an observation is a value built from
the environment's values and the constructors. -/
theorem runWith_obs (write : Array Slot → Slot → Array Slot) :
    ∀ {Γ : TyEnv} {e : Expr} {o : ObsDesc}, Obs Γ e o →
      ∀ {ρ : VEnv} {a : Array Slot}, WF Γ ρ → runWith write ρ a e = some (inst ρ e, a) := by
  intro Γ e o h
  induction h with
  | var x hx hf =>
      intro ρ a hwf
      obtain ⟨w, hw⟩ := hwf.exists_of_some hx
      simp only [runWith, inst, hw, Option.getD_some]
      rfl
  | unit => intro ρ a _; rfl
  | nat n => intro ρ a _; rfl
  | empty => intro ρ a _; rfl
  | full n =>
      intro ρ a _
      simp only [runWith, inst]
      rfl
  | pair ha hb iha ihb =>
      intro ρ a hwf
      simp only [runWith, inst, iha hwf, ihb hwf, Option.bind_some]
      rfl

/-- The instance of an observation is a denotation of its description. -/
theorem obs_denote : ∀ {Γ : TyEnv} {e : Expr} {o : ObsDesc}, Obs Γ e o →
    ∀ {ρ : VEnv}, WF Γ ρ → Denote o (inst ρ e) := by
  intro Γ e o h
  induction h with
  | var x hx hf =>
      intro ρ hwf
      obtain ⟨w, hw⟩ := hwf.exists_of_some hx
      have hden := hwf.2.2 x _ w hx hw
      simpa only [inst, hw, Option.getD_some] using hden
  | unit => intro ρ _; rfl
  | nat n => intro ρ _; exact ⟨n, rfl⟩
  | empty => intro ρ _; exact ⟨.empty, rfl⟩
  | full n => intro ρ _; exact ⟨.full n, rfl⟩
  | pair ha hb iha ihb =>
      intro ρ hwf
      obtain ⟨s, hs⟩ := iha hwf
      obtain ⟨t, ht⟩ := ihb hwf
      refine ⟨s, t, ?_⟩
      simp only [inst, hs, ht, quotePair]

/-! ## The simulation -/

/-- The shape of a result of an observation type: it carries no unary root node,
so the protected cell is never among the values an admitted program returns. -/
def ObsShape (τ : Ty) (v : Expr) : Prop := ∀ o, τ = .obs o → hasRoot v = false

/-- The shape of a result of cell type: it is the quoted root of the slot the
array holds afterwards. -/
def CellShape (τ : Ty) (v : Expr) (a : Array Slot) : Prop :=
  τ = .cell → ∃ s, v = root s ∧ a = #[s]

/-- Transitivity of the evaluation path. -/
theorem StepStar.trans : ∀ {a b c : Expr}, StepStar a b → StepStar b c → StepStar a c := by
  intro a b c h₁
  induction h₁ with
  | refl e => intro h₂; exact h₂
  | step hs _ ih => intro h₂; exact StepStar.step hs (ih h₂)

/-- A path of a binding's bound term lifts to the binding: one congruence step
per step of the term, and the empty path for the empty one. -/
theorem stepStar_bindFun (x : Var) (e₂ : Expr) : ∀ {e₁ e₁' : Expr},
    StepStar e₁ e₁' → StepStar (.bind x e₁ e₂) (.bind x e₁' e₂) := by
  intro e₁ e₁' h
  induction h with
  | refl e => exact StepStar.refl _
  | step hs _ ih => exact StepStar.step (Step.bindFun hs) ih

/-- The simulation: an admitted term, evaluated on one array and an environment
agreeing with its context, returns a value the copying λPure reduction of the
same term reaches — `StepStar (inst ρ e) v` is a statement about the existing
`Scidonia.RC.Step`, not about a second evaluator — and that value has the shape
its type gives it: an observation carries no root node, and a cell is the quoted
root of exactly the slot the array holds.

The one-cell invariant is an *input* assumption. It is what a read's borrowing
sees, and the hand-off re-establishes it for the continuation's fresh name from
the cell the bound term yielded; a write is never followed by the invariant at
the name that was consumed, because the binding that consumes it names the
fresh handle. -/
theorem runOn_simulate : ∀ {Γ : TyEnv} {κ : Owner} {e : Expr} {τ : Ty},
    Own Γ κ e τ → ∀ {ρ : VEnv} {arr : Array Slot}, WF Γ ρ → Inv Γ κ arr ρ →
      ∃ v arr', runOn ρ arr e = some (v, arr') ∧ StepStar (inst ρ e) v ∧ Value v ∧
        ObsShape τ v ∧ CellShape τ v arr' := by
  intro Γ κ e τ h
  induction h with
  | obs hobs =>
      intro ρ arr hwf _
      obtain ⟨hv, _, hnr⟩ := denote_shape (obs_fragment hobs) (obs_denote hobs hwf)
      exact ⟨_, arr, runWith_obs _ hobs hwf, StepStar.refl _, hv,
        fun o _ => hnr, fun hc => absurd hc (by simp)⟩
  | fresh hobs =>
      intro ρ arr hwf _
      obtain ⟨s, hs⟩ := obs_denote hobs hwf
      refine ⟨root s, #[s], ?_, ?_, root_value s, ?_, ?_⟩
      · simp only [runOn, runWith, runWith_obs _ hobs hwf, hs, Option.bind_some,
          unquoteSlot_quoteSlot, Option.map_some, root, ↓reduceIte]
      · show StepStar (inst ρ (.con1 rootTag _)) (root s)
        simp only [inst, hs, root]
        exact StepStar.refl (root s)
      · intro o hc
        exact absurd hc (by simp)
      · intro _
        exact ⟨s, rfl, rfl⟩
  | read x y body hx hy hbody ih =>
      intro ρ arr hwf hinv
      obtain ⟨s, hsρ, harr⟩ := hinv x rfl hx
      have hwf' := WF.extend_obs (y := y) hwf Fragment.slot ⟨s, rfl⟩
      have hinv' := Inv.extend_obs (y := y) (o := slotObs) (v := quoteSlot s) hinv
      have hpy : ρ y = none := (hwf.1 y).mp hy
      have hbinds : y ∉ binders body :=
        own_no_rebind hbody (by rw [TyEnv.extend_self]; simp)
      obtain ⟨v, arr', hrun₂, hstep₂, hv, hobs₂, hcell₂⟩ := ih hwf' hinv'
      refine ⟨v, arr', ?_, ?_, hv, hobs₂, hcell₂⟩
      · have hread : readCell arr = some s := by rw [harr]; exact readCell_singleton s
        simp only [runOn, runWith, hread, Option.bind_some, ↓reduceIte]
        exact hrun₂
      · simp only [inst, hsρ]
        refine StepStar.step (Root.toStep (Root.matchVal (s := root s) (c := rootTag)
          (ys := [y]) (body := inst ρ body) (root_value s) rfl (by simp [nodeFields, root]))) ?_
        simpa [nodeFields, root, substAll, subst_inst hpy (quoteSlot_closed s)
          (fun x' w hw => (hwf.2.1 x' w hw).2) body hbinds] using hstep₂
  | write x hx ha =>
      intro ρ arr hwf hinv
      obtain ⟨s, hsρ, harr⟩ := hinv x rfl hx
      obtain ⟨t, ht⟩ := obs_denote ha hwf
      refine ⟨root t, #[t], ?_, ?_, root_value t, ?_, ?_⟩
      · have hset : (#[s] : Array Slot).set! 0 t = #[t] := set_singleton s t
        have hguard : 0 < (#[s] : Array Slot).size := by simp
        simp only [runOn, runWith, runWith_obs _ ha hwf, ht, Option.bind_some,
          unquoteSlot_quoteSlot, Option.map_some, harr, root, ↓reduceIte, hguard, hset]
      · refine StepStar.step (Root.toStep ?_) (StepStar.refl (root t))
        simp only [inst, hsρ, ht, root]
        exact Root.storeVal (root_value s) (quoteSlot_value t) (slotUpdate_root s t)
      · intro o hc
        exact absurd hc (by simp)
      · intro _
        exact ⟨t, rfl, rfl⟩
  | cellBind y e₁ e₂ h₁ hy h₂ ih₁ ih₂ =>
      intro ρ arr hwf hinv
      obtain ⟨v₁, arr₁, hrun₁, hstep₁, _, _, hcell₁⟩ := ih₁ hwf hinv
      obtain ⟨s, rfl, rfl⟩ := hcell₁ rfl
      have hwf' := WF.extend_cell (y := y) hwf (root_value s) (root_closed s)
      have hpy : ρ y = none := (hwf.1 y).mp hy
      have hbinds : y ∉ binders e₂ :=
        own_no_rebind h₂ (by rw [TyEnv.extend_self]; simp)
      obtain ⟨v, arr', hrun₂, hstep₂, hv, hobs₂, hcell₂⟩ :=
        ih₂ hwf' (Inv.extend_cell (ρ := ρ) (y := y) (s := s))
      refine ⟨v, arr', ?_, ?_, hv, hobs₂, hcell₂⟩
      · simp only [runOn, runWith, hrun₁, Option.bind_some]
        exact hrun₂
      · rw [show inst ρ (.bind y e₁ e₂) = .bind y (inst ρ e₁) (inst ρ e₂) from rfl]
        refine StepStar.trans (stepStar_bindFun y (inst ρ e₂) hstep₁) ?_
        refine StepStar.step (Root.toStep (Root.bindVal (root_value s))) ?_
        simpa [subst_inst hpy (root_closed s) (fun x' w hw => (hwf.2.1 x' w hw).2) e₂ hbinds]
          using hstep₂
  | obsBind y e₁ e₂ h₁ hy h₂ ih =>
      intro ρ arr hwf hinv
      obtain ⟨hv1, hc1, _⟩ := denote_shape (obs_fragment h₁) (obs_denote h₁ hwf)
      have hwf' := WF.extend_obs (y := y) hwf (obs_fragment h₁) (obs_denote h₁ hwf)
      have hpy : ρ y = none := (hwf.1 y).mp hy
      have hbinds : y ∉ binders e₂ :=
        own_no_rebind h₂ (by rw [TyEnv.extend_self]; simp)
      obtain ⟨v, arr', hrun₂, hstep₂, hv, hobs₂, hcell₂⟩ :=
        ih hwf' (Inv.extend_obs (y := y) (v := inst ρ e₁) hinv)
      refine ⟨v, arr', ?_, ?_, hv, hobs₂, hcell₂⟩
      · simp only [runOn, runWith, runWith_obs _ h₁ hwf, Option.bind_some]
        exact hrun₂
      · rw [show inst ρ (.bind y e₁ e₂) = .bind y (inst ρ e₁) (inst ρ e₂) from rfl]
        refine StepStar.step (Root.toStep (Root.bindVal hv1)) ?_
        simpa [subst_inst hpy hc1 (fun x' w hw => (hwf.2.1 x' w hw).2) e₂ hbinds]
          using hstep₂

end OwnershipTyped

end Scidonia.RC
