def find : Nat → Array UInt64 → Nat → Array UInt64 × Nat
  | 0, parent, x => (parent, x)
  | fuel + 1, parent, x =>
    let px := parentOf parent x
    if px = x then (parent, x)
    else
      let gx := parentOf parent px
      find fuel (writeWord parent x gx.toUInt64) gx
