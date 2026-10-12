theorem snapshot_after_write {ℓ : Loc} {o : ReadOp} {w : WriteOp} {h h' : Heap σ}
    {b : Bool} {v v' : inst.Result o}
    (hr : ReadAt inst ℓ o h h v) (hw : WriteAt inst ℓ w h h' b)
    (hr' : ReadAt inst ℓ o h' h' v') :
    ∃ s, At ℓ s h ∧ v = inst.observe o s ∧
      v' = inst.observe o (inst.replace w s).1 := by
