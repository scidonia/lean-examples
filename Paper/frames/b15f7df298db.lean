theorem wf_sharesPositive : ∀ {t : Thread inst α}, ∀ {q : Rat}, WF inst q t → 0 < q →
    sharesPositive inst t := by
