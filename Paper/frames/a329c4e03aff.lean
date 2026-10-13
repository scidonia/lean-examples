theorem alias_bind_no_typing {Δ Γ : Occs} {x z : Var} {i : Nat} {v : Expr} :
    ¬ Typed Δ Γ (.bind x (.var z) (.store (.var x) i v)) := by
