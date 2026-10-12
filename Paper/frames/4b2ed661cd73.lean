theorem sealedSnapshot {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (s s' : σ) (old : Value)
    (new : ObsEl p.obs) (hread : read? p s = some old)
    (hwrite : setLeaf p new s = (s', true)) :
    read? p s = some old ∧ read? p s' = some (encodeObs p.obs new) := by
