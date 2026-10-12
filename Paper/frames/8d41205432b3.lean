theorem arrayReplace_bounds (a : Array UInt64) (w : ArrayWriteOp) :
    (arrayReplace w a).2 = true ↔ w.1 < a.size := by
