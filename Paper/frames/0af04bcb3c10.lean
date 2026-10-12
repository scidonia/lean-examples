theorem sealedRead_after_setLeaf {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (x : ObsEl p.obs) (s : σ)
    (h : (setLeaf p x s).2 = true) :
    read? p (setLeaf p x s).1 = some (encodeObs p.obs x) := by
