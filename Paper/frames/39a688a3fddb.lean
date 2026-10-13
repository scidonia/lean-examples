def Counted (c : CHeap) (handles : List Ref) : Prop :=
  ∀ r, CHeap.count c r = refCount (CHeap.presentation c) handles r
