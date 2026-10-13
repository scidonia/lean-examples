theorem disjoint_left_iff {a b : Layout} {p q : Path a} :
    Disjoint (.left p : Path (.struct a b)) (.left q) ↔ Disjoint p q := by
