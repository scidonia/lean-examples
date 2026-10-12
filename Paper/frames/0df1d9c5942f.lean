theorem complete_run_value {s : Array UInt64}
    (h : StepStar s (.run 1 t) (.run 1 (.pure a))) : a = val s t :=
