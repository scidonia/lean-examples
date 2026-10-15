def nestedSet (a : Array (Array UInt64)) (i j : Nat) (v : UInt64) :
    Array (Array UInt64) × Bool :=
  SealedStateVar.setLeaf (σ := Array (Array UInt64)) (nestedPath i j) v a
