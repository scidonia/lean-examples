theorem exclusive_head {c : CHeap} {hs : List Ref} {r : Ref}
    (hes : Exclusive (CHeap.presentation c) hs r) (hhead : hs.head? = some r) :
    (CHeap.slots c).count r = 0 ∧ hs.count r = 1 ∧ hs.tail.count r = 0 := by
