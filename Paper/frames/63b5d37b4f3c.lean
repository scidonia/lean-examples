abbrev Heap (σ : Type) := Loc → Option σ

def At {σ : Type} (ℓ : Loc) (s : σ) (h : Heap σ) : Prop := h ℓ = some s
