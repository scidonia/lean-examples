inductive TCtx where
  | hole
  | appL (E : TCtx) (a : Expr)
  | appR (f : Expr) (E : TCtx)
  | bindL (x : Var) (E : TCtx) (e₂ : Expr)
  | con1L (ct : Ctor) (E : TCtx)
  | con2L (ct : Ctor) (E : TCtx) (b : Expr)
  | con2R (ct : Ctor) (a : Expr) (E : TCtx)
