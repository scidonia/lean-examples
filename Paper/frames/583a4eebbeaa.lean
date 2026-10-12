theorem replay_trace (s : σ) (t : RT inst α) :
    replay (inst := inst) t (run (inst := inst) s t).2 = some (val (inst := inst) s t, []) := by
