theorem snapshot_after_setLeaf {d : Layout} (p : ObsPath d) (s s' : State d)
    (old : Value) (new : ObsEl p.obs) (hread : read? p s = some old)
    (hwrite : setLeaf p new s = (s', true)) :
    read? p s = some old ∧ read? p s' = some (encodeObs p.obs new) := by
