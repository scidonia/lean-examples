def arrayObserve (o : ArrayReadOp) (a : Array UInt64) : ArrayResult o :=
  match o with
  | .get i => a[i]?
  | .size => a.size

def arrayReplace (w : ArrayWriteOp) (a : Array UInt64) : Array UInt64 × Bool :=
  if w.1 < a.size then (a.set! w.1 w.2, true) else (a, false)

def encodeArrayRead : (o : ArrayReadOp) → ArrayResult o → Value
  | .get _, none => .none
  | .get _, some x => .some (.uint x)
  | .size, n => .nat n
