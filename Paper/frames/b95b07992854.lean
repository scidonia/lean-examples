def writeWord (a : Array UInt64) (i : Nat) (v : UInt64) : Array UInt64 :=
  (SealedStateVar.setLeaf (σ := Array UInt64) (wordPath i) v a).1
