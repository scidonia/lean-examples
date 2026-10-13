theorem universe_write_at_frame (d : Desc) {ℓ m : Loc} {x : El d}
    {h h' : Heap (Described d)} {b : Bool}
    (hw : WriteAt (describedStateVar d) ℓ x h h' b) (hm : m ≠ ℓ) : h' m = h m :=
