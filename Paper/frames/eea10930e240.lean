theorem store_shared_copies {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var}
    {r : Ref} {i : Nat} {v : Expr} {ks : List Ref} (hc : Couple c hs ρ m)
    (hρ : ρ.lookup y = some r) (hown : Owns ρ m (.store (.var y) i v))
    (hm : 2 ≤ (expand m).count r ∨ 1 ≤ (CHeap.slots c).count r) (hks : r ∉ ks) :
    (update c (hs ++ expand m) r ks).1.lookup (fresh c ks) = some ks ∧
      (update c (hs ++ expand m) r ks).1.lookup r = CHeap.lookup c r ∧
      (update c (hs ++ expand m) r ks).1.count r = CHeap.count c r - 1 := by
