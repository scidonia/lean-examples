def Couple (c : CHeap) (hs : List Ref) (ρ : TEnv) (m : Multi) : Prop :=
  CHeap.WF c ∧ Counted c (hs ++ expand m) ∧ Bound ρ m
