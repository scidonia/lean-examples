def Fits (Δ Γ : Occs) (e : Expr) : Prop := ∀ x ∈ uses e, x ∈ Γ ∨ x ∈ Δ
