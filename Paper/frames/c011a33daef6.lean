theorem noRef_pair {ℓ : Loc} {x y : Value} :
    NoRef ℓ (.pair x y) ↔ NoRef ℓ x ∧ NoRef ℓ y := Iff.rfl
