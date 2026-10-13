theorem lower_deterministic {Δ Γ : Occs} {e e₁ e₂ : Expr} (h₁ : Lower Δ Γ e e₁)
    (h₂ : Lower Δ Γ e e₂) : e₁ = e₂ := by
  have hb₁ := lowerB_complete h₁
