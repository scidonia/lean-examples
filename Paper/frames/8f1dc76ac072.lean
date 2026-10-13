theorem pstep_write_corresponds {α : Type} {s : σ} {w : WriteOp} {k : Bool → PT inst α}
    {ℓ : Loc} {h h' : Heap σ} {c' : PConf inst}
    (hstep : PStep inst (.exclusive s (.write w k)) c') (hat : At ℓ s h)
    (hs : inst.Valid s) (hh' : h' = Heap.update h ℓ (some (inst.replace w s).1)) :
    c' = .exclusive (inst.replace w s).1 (k (inst.replace w s).2) ∧
      WriteAt inst ℓ w h h' (inst.replace w s).2 :=
