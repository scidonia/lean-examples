structure HSt (σ : Type) (P : Pre σ) (β : Type) (Q : Post σ β) where
  private mk ::
  private run : Cap → (s : σ) → (∃ l, P l s) →
    { r : β × σ // ∀ l, P l s → ∃ l', Q l s r.1 l' r.2 }
