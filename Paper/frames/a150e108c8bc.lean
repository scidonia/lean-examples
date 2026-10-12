theorem sealedLawful_Result {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) :
    (sealedLawful (σ := σ)).Result p = Option (ObsEl p.obs) := rfl
