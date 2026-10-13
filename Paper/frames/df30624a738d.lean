theorem writeStep_nested_destructive_of_couple {root : Ref} {c : CHeap} {hs : List Ref}
    {vs : List Scidonia.FracPerm.StateVar.Value} {ρ : TEnv} {m : Multi} {i : Nat}
    {p : Path} {ks : List Ref}
    {e : Ref} {c' : CHeap} {hs' : List Ref} {Γ Δ : Occs} {y : Var} {j : Nat} {v : Expr}
    (hacc : Accept root c hs vs)
    (hstep : writeStep c hs root (i :: p) ks = some (c', hs'))
    (hlook : (CHeap.slotsAt c root)[i]? = some e)
    (hbound : Bound ρ m) (hsize : expand m = [e]) (hks : e ∉ ks)
    (hname : ∀ x, countName m x = Γ.count x) (hlookup : ρ.lookup y = some e)
    (hstore : Typed Δ Γ (.store (.var y) j v)) :
    Couple (held c root i e) hs ρ m ∧
      (update (held c root i e) (e :: hs) e ks).1.lookup e = some ks ∧
      hs' = hs ∧ ∃ t, resolve c root (i :: p) = some t ∧ c'.lookup t = some ks := by
