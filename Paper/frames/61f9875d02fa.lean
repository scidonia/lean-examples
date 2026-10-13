def read? {d : Layout} (p : ObsPath d) (s : State d) : Option Value :=
  (leafAt? p.path p.obs p.leaf s).map (encodeObs p.obs)
