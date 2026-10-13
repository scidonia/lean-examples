theorem takeOut_refCount_eq_one (rc0 rc1 rc2 : Int32)
    (hcell : refCount rc0 = 1)
    (hhand : refCount rc1 = refCount rc0 + 1)
    (hrelease : refCount rc2 = refCount rc1 - 1) :
    refCount rc2 = 1 := by
