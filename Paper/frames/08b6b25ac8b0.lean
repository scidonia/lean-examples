theorem reading_step_store {s s' : Array UInt64} {th th' : Thread β} {k : β → PTree α}
    (h : PStep (.reading s th k) (.reading s' th' k)) : s' = s := by
