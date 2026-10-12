theorem step_size {s : Array UInt64} {q : Rat} {k : Nat → RTree α} {u : Thread α}
    (h : Step s (.run q (.size k)) u) : u = .run q (k s.size) := by
