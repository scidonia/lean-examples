inductive Layout where
  | leaf (o : ObsDesc)
  | struct (left right : Layout)
  | arr (elem : Layout)
deriving DecidableEq, Repr

abbrev State : Layout → Type
  | .leaf o => ObsEl o
  | .struct a b => State a × State b
  | .arr a => Array (State a)
