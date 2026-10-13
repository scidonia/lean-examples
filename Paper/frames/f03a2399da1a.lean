theorem set_step {s : Array UInt64} {i : Nat} {v : UInt64} {k : Bool → PTree α}
    {c' : PConf} (h : PStep (.exclusive s (.set i v k)) c') :
    c' = .exclusive (if i < s.size then s.set! i v else s) (k (decide (i < s.size))) := by
