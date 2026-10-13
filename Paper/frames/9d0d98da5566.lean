inductive Typed : Occs → Occs → Expr → Prop where
  | var {Δ Γ : Occs} {x : Var} (h : x ∈ Γ ∨ x ∈ Δ) : Typed Δ Γ (.var x)
  | lam {Δ Γ : Occs} {x : Var} {body : Expr}
      (hlin : writes x body = true → (uses body).count x = 1)
      (h : Typed (forget Δ x) (bindEnv Γ x (uses body)) body) : Typed Δ Γ (.lam x body)
