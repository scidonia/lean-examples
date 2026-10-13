theorem refInj_of_counted {c : CHeap} {hs : List Ref} {m : Multi} {e : Ref}
    (hrun : Counted c (e :: hs)) (hcouple : Counted c (hs ++ expand m)) : RefInj m :=
