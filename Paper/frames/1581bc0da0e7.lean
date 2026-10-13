theorem lower_total {Δ Γ : Occs} {e : Expr} (hp : Pure e) (hfit : Fits Δ Γ e) :
    ∃ e', Lower Δ Γ e e' := by
