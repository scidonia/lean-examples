theorem step_deterministic : ∀ {e e₁ : Expr}, Step e e₁ →
    ∀ {e₂ : Expr}, Step e e₂ → e₁ = e₂ := by
