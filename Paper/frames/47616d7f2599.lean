def source : Expr := .bind 0 (.con2 7 (.var 1) (.var 2)) (.store (.var 0) 0 (.var 2))

def lowered : Expr :=
  .dup 2 (.drop 0 (.bind 0 (.con2 7 (.var 1) (.var 2)) (.store (.var 0) 0 (.var 2))))
