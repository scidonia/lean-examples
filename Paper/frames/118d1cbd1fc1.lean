def encodeObs : (o : ObsDesc) → ObsEl o → Value
  | .unit, _ => .unit
  | .nat, n => .nat n
  | .uint, n => .uint n
  | .bool, b => .bool b
  | .sum a _, Sum.inl x => .inl (encodeObs a x)
  | .sum _ b, Sum.inr y => .inr (encodeObs b y)
  | .option _, none => .none
  | .option a, some x => .some (encodeObs a x)
  | .pair a b, (x, y) => .pair (encodeObs a x) (encodeObs b y)
