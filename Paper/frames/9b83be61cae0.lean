theorem sealedRead_frame {σ : Type} [SealedStateVar σ]
    (p q : ObsPath (SealedStateVar.layout (σ := σ))) (s s' : σ) (new : ObsEl p.obs)
    (hdisjoint : Disjoint p.path q.path) (hwrite : setLeaf p new s = (s', true)) :
    read? q s' = read? q s := by
