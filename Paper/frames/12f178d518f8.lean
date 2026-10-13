theorem disjoint_index_ne {a : Layout} {p q : Path a} {i j : Nat} (h : i ≠ j) :
    Disjoint (.index i p : Path (.arr a)) (.index j q) :=
