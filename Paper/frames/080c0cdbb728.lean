  | store {Δ Γ : Occs} {y : Var} {i : Nat} {v : Expr} (hown : Γ.count y = 1)
      (hborrow : y ∉ Δ) (hv : Typed Δ (claimEnv Γ (uses v)) v) :
      Typed Δ Γ (.store (.var y) i v)
