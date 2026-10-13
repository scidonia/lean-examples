def setLeaf {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (x : ObsEl p.obs) : σ → σ × Bool :=
  fun s =>
    let r := Layout5.setLeaf p x (toState s)
    (ofState r.1, r.2)
