theorem append_left {a b : Layout} (p : Path a) (q : Path (At p)) :
    Path.append (.left p : Path (.struct a b)) q = .left (Path.append p q) := rfl
