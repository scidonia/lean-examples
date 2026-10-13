theorem safe_result {ℓ : Loc} {α : Type} {P : α → Prop} {t : RT inst α} {s : σ}
    (ht : SafeTree inst ℓ α P t) (hs : inst.Valid s) : P (val s t) := by
