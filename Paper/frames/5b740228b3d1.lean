theorem read_at_detached {ℓ : Loc} {o : ReadOp} {h h' : Heap σ} {v : inst.Result o}
    (hr : ReadAt inst ℓ o h h' v) : NoRef ℓ (inst.encodeRead o v) := by
