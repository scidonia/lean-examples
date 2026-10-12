theorem append_right {a b : Layout} (p : Path b) (q : Path (At p)) :
    Path.append (.right p : Path (.struct a b)) q = .right (Path.append p q) := rfl
