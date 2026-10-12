def Disjoint {d : Layout} (p q : Path d) : Prop :=
  (∀ r : Path (At p), q ≠ Path.append p r) ∧ (∀ r : Path (At q), p ≠ Path.append q r)
