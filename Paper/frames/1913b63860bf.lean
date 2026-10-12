theorem held_erase_of_mem {n : Nat} {q : Rat} {l : Ledger} (h : (n, q) ∈ l) :
    held (l.erase (n, q)) = held l + q := by
