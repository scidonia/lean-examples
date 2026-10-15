def unionStepsAliased : Nat → List (Nat × Nat) → Array UInt64 → Array UInt64 →
    Nat → IO (Array UInt64 × Array UInt64 × Nat)
  | _, [], parent, rank, total => return (parent, rank, total)
  | fuel, (x, y) :: rest, parent, rank, total => do
    let aliasParent := parent
    let aliasRank := rank
    let (parent', rank') := union fuel parent rank x y
    let parentHere ← addressIO aliasParent
    let rankHere ← addressIO aliasRank
    let seen := ((aliasParent[x]?).map UInt64.toNat).getD 0
      + ((aliasRank[y]?).map UInt64.toNat).getD 0
    unionStepsAliased fuel rest parent' rank'
      (total + parentHere.toNat + rankHere.toNat + seen)
