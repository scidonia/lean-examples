theorem couple_of_takeout {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {r : Ref}
    {i : Nat} {e : Ref} (hW : CHeap.WF c) (hcounted : Counted c hs)
    (hhead : hs.head? = some r) (hex : Exclusive (CHeap.presentation c) hs r)
    (hlook : (CHeap.slotsAt c r)[i]? = some e)
    (hbound : Bound ρ m) (hsize : expand m = [e]) :
    Couple (held c r i e) hs ρ m := by
