theorem held_cons (n : Nat) (q : Rat) (l : Ledger) : held ((n, q) :: l) = held l - q := by
