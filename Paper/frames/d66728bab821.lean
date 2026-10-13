theorem lifted_iff (P : Slot → Prop) (s : Slot) : P s ↔ P (decode (encode s)) := by
