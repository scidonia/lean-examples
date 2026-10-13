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
