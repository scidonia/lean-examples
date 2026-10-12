theorem universe_snapshot_after_write (d : Desc) {ℓ : Loc} {x : El d}
    {h h' : Heap (Described d)} {b : Bool} {v v' : El d}
    (hr : ReadAt (describedStateVar d) ℓ () h h v)
    (hw : WriteAt (describedStateVar d) ℓ x h h' b)
    (hr' : ReadAt (describedStateVar d) ℓ () h' h' v') :
    ∃ s, At ℓ s h ∧ v = (describedStateVar d).observe () s ∧
      v' = (describedStateVar d).observe () ((describedStateVar d).replace x s).1 :=
