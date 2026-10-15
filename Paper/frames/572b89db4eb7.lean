def treeSet (k : Nat) (v : UInt64) (t : Layout5.State (structTree k)) :
    Layout5.State (structTree k) × Bool :=
  SealedStateVar.setLeaf (σ := Layout5.State (structTree k)) (treePath k) v t
