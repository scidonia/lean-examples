theorem universe_write_at_valid (d : Desc) {ℓ : Loc} {x : El d}
    {h h' : Heap (Described d)} {b : Bool}
    (hw : WriteAt (describedStateVar d) ℓ x h h' b) :
    ∃ s', At ℓ s' h' ∧ (describedStateVar d).Valid s' :=
