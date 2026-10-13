  | matchC {Δ Γ : Occs} {s : Expr} {c : Ctor} {ys : List Var} {body : Expr}
      (hlin : ∀ y ∈ ys, writes y body = true → (uses body).count y = 1)
      (hbuild : ∀ y ∈ ys, writes y body = true → BuiltB s = true)
      (hs : Typed Δ (claimEnv Γ (uses s)) s)
      (h : Typed (forgetAll Δ ys) (armEnv Γ ys (uses body)) body) :
      Typed Δ Γ (.matchC s c ys body)
