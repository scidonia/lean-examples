theorem slot_snapshot_full7_full9 {ℓ : Loc} {h h' : Heap Slot}
    (hat : At ℓ (Slot.full 7) h)
    (hw : WriteAt slotStateVar ℓ (Slot.full 9) h h' true) :
    ReadAt slotStateVar ℓ () h h (Slot.full 7) ∧ At ℓ (Slot.full 9) h' ∧
      At ℓ (Slot.full 7) h := by
