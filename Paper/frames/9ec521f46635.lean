  cast (SealedStateVar.rep (σ := σ)) s

def read? {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) : σ → Option Value :=
  fun s => Layout5.read? p (toState s)
