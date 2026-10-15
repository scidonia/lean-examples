def structTree : Nat → Layout5.Layout
  | 0 => .leaf .uint
  | k + 1 => .struct (structTree k) (structTree k)
