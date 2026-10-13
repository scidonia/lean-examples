inductive Step : Expr → Expr → Prop where
  | root {e e' : Expr} : Root e e' → Step e e'
  | appFun {f f' a : Expr} : Step f f' → Step (.app f a) (.app f' a)
  | appArg {f a a' : Expr} : Value f → Step a a' → Step (.app f a) (.app f a')
  | bindFun {e₁ e₁' : Expr} {x : Var} {e₂ : Expr} : Step e₁ e₁' →
      Step (.bind x e₁ e₂) (.bind x e₁' e₂)
