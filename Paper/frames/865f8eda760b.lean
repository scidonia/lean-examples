theorem sealedRead_detached {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (s : σ) (v : Value)
    (h : read? p s = some v) (ℓ : Loc) : NoRef ℓ v :=
