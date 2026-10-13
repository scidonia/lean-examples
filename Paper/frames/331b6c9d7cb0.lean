theorem step_get {s : Array UInt64} {q : Rat} {i : Nat} {k : Option UInt64 → RTree α}
    {u : Thread α} (h : Step s (.run q (.get i k)) u) : u = .run q (k s[i]?) := by
