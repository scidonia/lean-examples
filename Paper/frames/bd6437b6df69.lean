theorem eval_of_run {s : σ} {t : RT inst α} {t' : Thread inst α}
    (h : StepStar inst s (.run 1 t) t') (ha : Eval inst s t' a) : a = val s t := by
