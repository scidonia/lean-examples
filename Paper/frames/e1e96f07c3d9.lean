theorem sealedSetLeaf_failed {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (x : ObsEl p.obs) (s : σ)
    (h : (setLeaf p x s).2 = false) : (setLeaf p x s).1 = s := by
