def dupValue : Expr := .lam 0 (.con1 7 (.store (.var 0) 0 (.var 0)))

def ownedValue : Expr := .lam 0 (.con1 7 (.store (.var 0) 0 (.con0 9)))

def dupArm : Expr := .matchC (.con1 5 (.con0 5)) 0 [0, 0] (.store (.var 0) 0 (.con0 9))

def ownedArm : Expr := .matchC (.con1 5 (.con0 5)) 0 [0] (.store (.var 0) 0 (.con0 9))

def siblingUse : Expr := .lam 0 (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.var 0)))

def siblingOwned : Expr := .lam 0 (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.con0 10)))

def aliasBind : Expr := .bind 0 (.var 1) (.store (.var 0) 0 (.con0 9))

def builtBind : Expr := .bind 0 (.con1 5 (.con0 5)) (.store (.var 0) 0 (.con0 9))
