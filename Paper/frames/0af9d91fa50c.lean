theorem update_copies_of_shared {c : CHeap} {handles : List Ref} (hc : Counted c handles)
    {r : Ref} {ks : List Ref} (h2 : ¬ Exclusive (CHeap.presentation c) handles r)
    (hhandle : 1 ≤ handles.count r) (hks : r ∉ ks) :
    (update c handles r ks).1.lookup (fresh c ks) = some ks ∧
      (update c handles r ks).1.lookup r = CHeap.lookup c r ∧
      (update c handles r ks).1.count r = CHeap.count c r - 1 ∧
      fresh c ks ∉ CHeap.refs c := by
