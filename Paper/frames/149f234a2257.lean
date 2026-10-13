structure Corr (ρ : TEnv) (m : Multi) (Γ : Occs) : Prop where
  bound : Bound ρ m
  name : ∀ x, countName m x = Γ.count x
  inj : RefInj m
