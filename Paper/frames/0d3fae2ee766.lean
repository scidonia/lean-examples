  | lam {Δ Γ : Occs} {x : Var} {body : Expr}
      (hlin : writes x body = true → (uses body).count x = 1)
      (h : Typed (forget Δ x) (bindEnv Γ x (uses body)) body) : Typed Δ Γ (.lam x body)
