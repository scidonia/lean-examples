theorem arrayObserve_detached (ℓ : Loc) (o : ArrayReadOp) (a : Array UInt64) :
    NoRef ℓ (encodeArrayRead o (arrayObserve o a)) := by
