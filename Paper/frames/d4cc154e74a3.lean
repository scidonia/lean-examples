theorem wait_step {s : σ} {q : Rat} {α β γ : Type} {l : Thread inst β}
    {r : Thread inst γ} {k : β × γ → RT inst α} {u : Thread inst α}
    (h : Step inst s (.wait q l r k) u) :
    (∃ q' l' r', u = .wait q' l' r' k) ∨
    (∃ (q₁ q₂ : Rat) (b : β) (c : γ),
      l = .run q₁ (.pure b) ∧ r = .run q₂ (.pure c) ∧ u = .run q (k (b, c))) := by
