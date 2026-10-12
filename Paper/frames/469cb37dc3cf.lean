theorem wf_sharesPositive : ∀ {t : Thread α}, ∀ {q : Rat}, WF q t → 0 < q →
    sharesPositive t := by
