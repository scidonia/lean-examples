theorem run_never_exclusive (rc : Int32) (ops : List Op) (h : isNeverFreed rc) :
    ∃ rc', run (some rc) ops = some rc' ∧ ¬ IsExclusive rc' := by
