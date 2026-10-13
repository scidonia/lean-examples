theorem couple_does_not_give_count_one :
    Couple ([(0, { slots := [], count := 2 })] : CHeap) [] aliasEnv aliasM
      ∧ Typed ([] : Occs) ([0,1] : Occs) (.store (.var 0) 0 (.con0 9))
      ∧ countName aliasM 0 = ([0,1] : Occs).count 0
      ∧ (expand aliasM).count (0 : Ref) ≠ 1 :=
