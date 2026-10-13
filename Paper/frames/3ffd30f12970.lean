theorem refInj_not_determined :
    ∃ m₁ m₂ : Multi, expand m₁ = expand m₂ ∧ RefInj m₁ ∧ ¬ RefInj m₂ ∧
      (∀ (c : CHeap) (hs : List Ref), Counted c (hs ++ expand m₁) ↔ Counted c (hs ++ expand m₂)) := by
