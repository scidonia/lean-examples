structure Cell where
  slots : List Ref
  count : Nat
deriving DecidableEq, Repr

abbrev CHeap := List (Ref × Cell)
