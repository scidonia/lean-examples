abbrev Multi := List (Var × Ref)

def expand (m : Multi) : List Ref := m.map (fun p => p.2)
