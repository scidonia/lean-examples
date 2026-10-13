private def setAt : {d : Layout} → (p : Path d) → State (At p) → State d → State d
  | _, .here, y, _ => y
  | _, .left q, y, (u, v) => (setAt q y u, v)
  | _, .right q, y, (u, v) => (u, setAt q y v)
  | _, .index i q, y, s =>
      if h : i < s.size then
        match takeOutAt (assertExclusiveArray openSite s) i h (stateDefault _) with
        | ⟨(sib, focus), hbound⟩ =>
          plugAt sib i hbound (setAt q y (assertExclusive structSite focus))
      else s

@[simp] private theorem inBounds_here {d : Layout} (s : State d) :
    inBounds (Path.here : Path d) s = true := rfl
