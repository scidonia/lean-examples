theorem replay_trace (s : Array UInt64) (t : RTree α) :
    replay t (run s t).2 = some (val s t, []) := by
