theorem sealedLawful_encodeRead {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (r : Option (ObsEl p.obs)) :
    (sealedLawful (σ := σ)).encodeRead p r =
      (describedLayoutStateVar (SealedStateVar.layout (σ := σ))).encodeRead p r := rfl
