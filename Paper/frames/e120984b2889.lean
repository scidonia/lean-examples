  | storeExclusive {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {i : Nat}
      {v : Expr} {c₁ : CHeap} {hs₁ : List Ref} {wv r : Ref} (hρ : ρ.lookup y = some r)
      (hv : ValRef c hs ρ v c₁ hs₁ wv) (hi : i < (CHeap.slotsAt c₁ r).length)
      (hchk : writeCheck c₁ r (storeSlots c₁ r i wv) = true) (h1 : CHeap.count c₁ r = 1)
      (hsub : (y, r) ∈ m) :
      TStep c hs ρ m (.store (.var y) i v)
        (update c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv)).1 hs₁ ρ m (.var y)
  | storeShared {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {i : Nat}
      {v : Expr} {c₁ : CHeap} {hs₁ : List Ref} {wv r : Ref} (hρ : ρ.lookup y = some r)
      (hv : ValRef c hs ρ v c₁ hs₁ wv) (hi : i < (CHeap.slotsAt c₁ r).length)
      (hchk : writeCheck c₁ r (storeSlots c₁ r i wv) = true) (hsub : (y, r) ∈ m)
      (hgone : nameGone m y r = true) (h2 : CHeap.count c₁ r ≠ 1) :
      TStep c hs ρ m (.store (.var y) i v)
        (update c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv)).1 hs₁
        (TEnv.set ρ y (fresh c₁ (storeSlots c₁ r i wv)))
        (Multi.insert (Multi.dropOcc m y r) y (fresh c₁ (storeSlots c₁ r i wv))) (.var y)
