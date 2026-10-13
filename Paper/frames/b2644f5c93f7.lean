  | bind {Δ Γ : Occs} {x : Var} {e₁ e₂ : Expr}
      (hlin : writes x e₂ = true → (uses e₂).count x = 1)
      (hbuild : writes x e₂ = true → BuiltB e₁ = true)
      (h₁ : Typed Δ (claimEnv Γ (uses e₁)) e₁)
      (h₂ : Typed (forget Δ x) (bindEnv Γ x (uses e₂)) e₂) : Typed Δ Γ (.bind x e₁ e₂)
