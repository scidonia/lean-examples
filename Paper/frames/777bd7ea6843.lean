theorem slot_read_after_replace (s t : Slot) :
    LawfulStateVar.observe () (LawfulStateVar.replace t s).1 = t :=
