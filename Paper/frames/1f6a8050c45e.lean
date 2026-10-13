def WriteAt {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp)
    (ℓ : Loc) (w : WriteOp) (h h' : Heap σ) (b : Bool) : Prop :=
  ∃ s, At ℓ s h ∧ inst.Valid s ∧
    h' = Heap.update h ℓ (some (inst.replace w s).1) ∧
    b = (inst.replace w s).2
