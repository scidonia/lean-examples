theorem read_detached {d : Layout} (p : ObsPath d) (s : State d) (v : Value)
    (h : read? p s = some v) (ℓ : Loc) : NoRef ℓ v := by
