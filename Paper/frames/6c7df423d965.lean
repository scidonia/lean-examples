def ReadAt {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp)
    (ℓ : Loc) (o : ReadOp) (h h' : Heap σ) (v : inst.Result o) : Prop :=
  ∃ s, At ℓ s h ∧ inst.Valid s ∧ h' = h ∧ v = inst.observe o s
