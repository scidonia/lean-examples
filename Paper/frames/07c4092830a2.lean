inductive ObsDesc where
  | unit
  | nat
  | uint
  | bool
  | sum (left right : ObsDesc)
  | option (elem : ObsDesc)
  | pair (left right : ObsDesc)
deriving DecidableEq, Repr

abbrev ObsEl : ObsDesc → Type
  | .unit => Unit
  | .nat => Nat
  | .uint => UInt64
  | .bool => Bool
  | .sum a b => Sum (ObsEl a) (ObsEl b)
  | .option a => Option (ObsEl a)
  | .pair a b => ObsEl a × ObsEl b
