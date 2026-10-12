theorem arrayReplace_size (a : Array UInt64) (w : ArrayWriteOp) :
    (arrayReplace w a).1.size = a.size := by
