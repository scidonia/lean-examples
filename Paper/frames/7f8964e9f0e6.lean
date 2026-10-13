theorem describedLayout_write_at_frame (d : Layout) {ℓ m : Loc} {w : LayoutWrite d}
    {h h' : Heap (DescribedLayout d)} {b : Bool}
    (hw : WriteAt (describedLayoutStateVar d) ℓ w h h' b) (hm : m ≠ ℓ) :
    h' m = h m :=
