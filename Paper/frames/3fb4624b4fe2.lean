theorem leakyArray_read_returns_state (a : Array UInt64) :
    LawfulStateVar.observe (self := leakyArrayStateVar) () a = a := rfl
