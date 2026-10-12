theorem eval_of_run {s : Array UInt64} {t : RTree α} {t' : Thread α}
    (h : StepStar s (.run 1 t) t') (ha : Eval s t' a) : a = val s t := by
