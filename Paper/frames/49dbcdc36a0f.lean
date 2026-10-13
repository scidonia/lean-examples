inductive Expr where
  | var (x : Var)
  | lam (x : Var) (body : Expr)
  | app (f a : Expr)
  | bind (x : Var) (e₁ e₂ : Expr)
  | matchC (s : Expr) (c : Ctor) (ys : List Var) (body : Expr)
  | dup (x : Var) (e : Expr)
  | drop (x : Var) (e : Expr)
  | con0 (c : Ctor)
  | con1 (c : Ctor) (a : Expr)
  | con2 (c : Ctor) (a b : Expr)
  | store (s : Expr) (i : Nat) (v : Expr)
  deriving DecidableEq, Repr
