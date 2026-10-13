theorem store_destructive_of_typed {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi}
    {Δ Γ : Occs} {y : Var} {r : Ref} {i : Nat} {v : Expr} {ks : List Ref}
    (hc : Couple c hs ρ m) (hcorr : Corr ρ m Γ) (hlook : ρ.lookup y = some r)
    (h : Typed Δ Γ (.store (.var y) i v))
    (hslot : (CHeap.slots c).count r = 0) (hrun : hs.count r = 0) (hks : r ∉ ks) :
    (update c (hs ++ expand m) r ks).1.lookup r = some ks := by
