theorem encodeArrayRead_injective (o : ArrayReadOp) (x y : ArrayResult o) :
    encodeArrayRead o x = encodeArrayRead o y → x = y := by
