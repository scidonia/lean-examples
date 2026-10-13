private def takeOut (s : Array α) (i : Nat) (h : i < s.size) (d : α) : Array α × α :=
  let r := s.swapAt i d h
  (r.2, r.1)
