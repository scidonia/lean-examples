def IsExclusive (rc : Int32) : Prop := isSt rc ∧ rc = 1

def IsUnshared (rc : Int32) : Prop := isUnshared rc
