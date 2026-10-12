theorem reading_step_store {s s' : σ} {th th' : Thread inst β} {k : β → PT inst α}
    (h : PStep inst (.reading s th k) (.reading s' th' k)) : s' = s := by
