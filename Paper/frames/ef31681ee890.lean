theorem reading_step_is_read_or_leave {s : σ} {th : Thread inst β}
    {k : β → PT inst α} {c' : PConf inst} (h : PStep inst (.reading s th k) c') :
    (∃ th', c' = .reading s th' k) ∨
    (∃ a, th = .run 1 (.pure a) ∧ c' = .exclusive s (k a)) := by
