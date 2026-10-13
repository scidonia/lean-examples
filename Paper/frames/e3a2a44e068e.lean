inductive Ectx where
  | hole
  | appL (E : Ectx) (a : Expr)
  | appR (f : Expr) (E : Ectx)
  | bindL (x : Var) (E : Ectx) (e₂ : Expr)
