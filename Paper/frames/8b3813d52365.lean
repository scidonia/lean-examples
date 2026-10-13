theorem slot_full_round_trip (n : Nat) : decode (encode (Slot.full n)) = Slot.full n :=
