theorem takeout_dropped_count_one {c : CHeap} {e : Ref} (hc : Counted c [e, e])
    (h0 : (CHeap.presentation c).occurrences e = 0) :
    (decRef c [e, e] e).1.count e = 1 ∧
      Exclusive (CHeap.presentation (decRef c [e, e] e).1) (decRef c [e, e] e).2 e := by
