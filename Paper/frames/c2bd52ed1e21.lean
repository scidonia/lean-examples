theorem not_exclusive_incRefN_one (rc : Int32) (h : IsExclusive rc) :
    ¬ IsExclusive (incRefN rc 1) := by
