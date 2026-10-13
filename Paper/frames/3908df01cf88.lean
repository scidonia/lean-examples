theorem set_step_size (s : Array UInt64) (i : Nat) (v : UInt64) :
    (if i < s.size then s.set! i v else s).size = s.size := by
