theorem expand_eq_singleton_of_counted {c : CHeap} {hs : List Ref} {m : Multi} {e : Ref}
    (hrun : Counted c (e :: hs)) (hcouple : Counted c (hs ++ expand m)) :
    expand m = [e] := by
