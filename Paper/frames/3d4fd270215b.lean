theorem append_index {a : Layout} (i : Nat) (p : Path a) (q : Path (At p)) :
    Path.append (.index i p) q = .index i (Path.append p q) := rfl
