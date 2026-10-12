class LawfulStateVar (σ : Type) (Init : outParam Type)
    (ReadOp : outParam Type) (WriteOp : outParam Type) where
  Result : ReadOp → Type
  initial : Init → σ
  Valid : σ → Prop
  observe : (o : ReadOp) → σ → Result o
  replace : WriteOp → σ → σ × Bool
  encodeRead : (o : ReadOp) → Result o → Value
  initial_valid : ∀ i : Init, Valid (initial i)
  replace_valid : ∀ (w : WriteOp) (s : σ),
    Valid s → Valid (replace w s).1
  encodeRead_injective : ∀ (o : ReadOp) (x y : Result o),
    encodeRead o x = encodeRead o y → x = y
  observe_detached : ∀ (ℓ : Loc) (o : ReadOp) (s : σ),
    Valid s → NoRef ℓ (encodeRead o (observe o s))
