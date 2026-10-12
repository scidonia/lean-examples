theorem encodeObs_noRef (ℓ : Loc) : ∀ (o : ObsDesc) (x : ObsEl o),
    NoRef ℓ (encodeObs o x)
