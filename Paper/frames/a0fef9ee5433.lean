theorem complete_run_value {s : σ} {t : RT inst α} {a : α}
    (h : StepStar inst s (.run 1 t) (.run 1 (.pure a))) : a = val s t :=
