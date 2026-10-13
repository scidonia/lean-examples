def Bound (ρ : TEnv) (m : Multi) : Prop := ∀ p ∈ m, ρ.lookup p.1 = some p.2
