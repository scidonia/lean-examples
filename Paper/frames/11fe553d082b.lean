theorem update_preserves_location_of_exclusive {c : CHeap} {handles : List Ref}
    (hW : CHeap.WF c) (hc : Counted c handles) {r : Ref} {ks : List Ref}
    (h1 : Exclusive (CHeap.presentation c) handles r) (hhandle : 1 ≤ handles.count r)
    (hks : r ∉ ks) :
    (update c handles r ks).1.lookup r = some ks := by
