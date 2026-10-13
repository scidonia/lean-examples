theorem n5_unreturned_read (a : Array Nat) :
    ¬ (∀ b l' a', HSt.post n5Prog [] a b l' a' → l'.held = 1) := by
