inductive Value : Expr → Prop where
  | var (x : Var) : Value (.var x)
  | lam (x : Var) (body : Expr) : Value (.lam x body)
  | con0 (c : Ctor) : Value (.con0 c)
  | con1 {c : Ctor} {a : Expr} (h : Value a) : Value (.con1 c a)
  | con2 {c : Ctor} {a b : Expr} (h₁ : Value a) (h₂ : Value b) : Value (.con2 c a b)
