class FracObject (σ : Type) (ReadOp : outParam Type) (WriteOp : outParam Type) where
  Result : ReadOp → Type
  observe : (o : ReadOp) → σ → Result o
  update : WriteOp → σ → σ

  check : String → WriteOp → σ → σ := fun site _ s => assertExclusive site s
  check_eq : ∀ site o s, check site o s = s
