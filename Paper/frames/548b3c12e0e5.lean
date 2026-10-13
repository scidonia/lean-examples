theorem write_at_frame {ℓ m : Loc} {w : WriteOp} {h h' : Heap σ} {b : Bool}
    (hw : WriteAt inst ℓ w h h' b) (hm : m ≠ ℓ) : h' m = h m := by
