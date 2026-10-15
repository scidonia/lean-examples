def union (fuel : Nat) (parent rank : Array UInt64) (x y : Nat) :
    Array UInt64 × Array UInt64 :=
  let (parent₁, rx) := find fuel parent x
  let (parent₂, ry) := find fuel parent₁ y
  if rx = ry then (parent₂, rank)
  else
    let rankX := rankOf rank rx
    let rankY := rankOf rank ry
    if rankX < rankY then (writeWord parent₂ rx ry.toUInt64, rank)
    else if rankY < rankX then (writeWord parent₂ ry rx.toUInt64, rank)
    else (writeWord parent₂ ry rx.toUInt64, writeWord rank rx (rankX + 1).toUInt64)
