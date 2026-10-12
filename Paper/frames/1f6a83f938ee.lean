def NoRef (ℓ : Loc) : Value → Prop
  | .loc k    => k ≠ ℓ
  | .some v   => NoRef ℓ v
  | .inl v    => NoRef ℓ v
  | .inr v    => NoRef ℓ v
  | .pair x y => NoRef ℓ x ∧ NoRef ℓ y
  | _         => True
