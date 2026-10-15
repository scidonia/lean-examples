def setLeaf {d : Layout} (p : ObsPath d) (x : ObsEl p.obs) (s : State d) :
    State d × Bool :=
  if inBounds p.path s then
    (setAt p.path (cast (congrArg State p.leaf.symm) x) s, true)
  else (s, false)
