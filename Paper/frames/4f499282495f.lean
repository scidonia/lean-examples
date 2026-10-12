theorem wait_step {s : Array UInt64} {q : Rat} {β γ : Type} {l : Thread β}
    {r : Thread γ} {k : β × γ → RTree α} {u : Thread α}
    (h : Step s (.wait q l r k) u) :
    (∃ q' l' r', u = .wait q' l' r' k) ∨
    (∃ (q₁ q₂ : Rat) (b : β) (c : γ),
      l = .run q₁ (.pure b) ∧ r = .run q₂ (.pure c) ∧ u = .run q (k (b, c))) := by
