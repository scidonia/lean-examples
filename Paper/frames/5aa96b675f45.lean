theorem reading_step_is_read_or_leave {s : Array UInt64} {th : Thread β}
    {k : β → PTree α} {c' : PConf} (h : PStep (.reading s th k) c') :
    (∃ th', c' = .reading s th' k) ∨
    (∃ a, th = .run 1 (.pure a) ∧ c' = .exclusive s (k a)) := by
