structure ObsPath (d : Layout) where
  path : Path d
  obs : ObsDesc
  leaf : At path = .leaf obs
