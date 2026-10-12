theorem write_at_valid {ℓ : Loc} {w : WriteOp} {h h' : Heap σ} {b : Bool}
    (hw : WriteAt inst ℓ w h h' b) : ∃ s', At ℓ s' h' ∧ inst.Valid s' := by
