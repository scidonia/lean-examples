theorem owns_of_correspondence {ρ : TEnv} {m : Multi} {Γ : Occs} {y : Var} {r : Ref}
    {i : Nat} {v : Expr} (hbound : Bound ρ m) (hname : countName m y = Γ.count y)
    (hone : Γ.count y = 1) (hlook : ρ.lookup y = some r) :
    Owns ρ m (.store (.var y) i v) := by
