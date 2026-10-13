theorem runs_store_owned {ρ : TEnv} {m : Multi} {y : Var} {i : Nat} {v : Expr}
    (h : Runs ρ m (.store (.var y) i v)) :
    Owns ρ m (.store (.var y) i v) ∧ ∃ r, ρ.lookup y = some r ∧ (expand m).count r = 1 := by
