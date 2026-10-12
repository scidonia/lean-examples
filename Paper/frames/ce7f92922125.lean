theorem readAt_step_observe {ℓ : Loc} {s : σ} {q : Rat} {o : ReadOp}
    {k : inst.Result o → RT inst α} {h h' : Heap σ} {v : inst.Result o}
    (hat : At ℓ s h) (hr : ReadAt inst ℓ o h h' v) :
    Step inst s (.run q (.read o k)) (.run q (k v)) := by
