theorem tstep_of_plug : ∀ {E : TCtx} {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi}
    {r e' : Expr} {c' : CHeap} {hs' : List Ref} {ρ' : TEnv} {m' : Multi},
    TCtx.WF E → TStep c hs ρ m r c' hs' ρ' m' e' →
      TStep c hs ρ m (E.plug r) c' hs' ρ' m' (E.plug e') := by
