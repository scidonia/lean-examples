inductive Path : Layout → Type where
  | here {d : Layout} : Path d
  | left {a b : Layout} (p : Path a) : Path (.struct a b)
  | right {a b : Layout} (p : Path b) : Path (.struct a b)
  | index {a : Layout} (i : Nat) (p : Path a) : Path (.arr a)
deriving DecidableEq

abbrev At {d : Layout} : Path d → Layout
  | .here => d
  | .left p => At p
  | .right p => At p
  | .index _ p => At p
