theorem slot_shape_change (n : Nat) {ℓ : Loc} {h₀ h₁ h₂ : Heap Slot} {b c : Bool}
    (h0 : At ℓ Slot.empty h₀)
    (hw1 : WriteAt slotStateVar ℓ (Slot.full n) h₀ h₁ b)
    (hw2 : WriteAt slotStateVar ℓ Slot.empty h₁ h₂ c) :
    b = true ∧ c = true ∧ At ℓ (Slot.full n) h₁ ∧ At ℓ Slot.empty h₂ ∧
      At ℓ Slot.empty h₀ := by
