theorem array_root_not_observable (o : ObsDesc) :
    At (Path.here : Path (.arr (.leaf .uint))) ≠ .leaf o := by
