theorem couple_step {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {e : Expr}
    {c' : CHeap} {hs' : List Ref} {ρ' : TEnv} {m' : Multi} {e' : Expr}
    (h : TStep c hs ρ m e c' hs' ρ' m' e') (hc : Couple c hs ρ m) : Couple c' hs' ρ' m' := by
