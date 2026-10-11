import Scidonia.FracPerm

open Scidonia.FracPerm.StateVar Layout5

/-- A write that reports failure leaves the state exactly as it was. The proof
is the whole of `setLeaf`'s gating: unfold the definition, split on the bounds
test, and take each branch. -/
theorem failed_write_leaves_state {d : Layout} (p : ObsPath d) (x : ObsEl p.obs)
    (s : State d) (h : (setLeaf p x s).2 = false) :
    (setLeaf p x s).1 = s := by
  -- slide-step
  unfold setLeaf at h ⊢
  -- slide-step
  split
  -- slide-step
  case isTrue => simp_all
  -- slide-step
  case isFalse => rfl

/-- A failed write is invisible to a subsequent read, at any path. -/
theorem failed_write_invisible {d : Layout} (p q : ObsPath d) (x : ObsEl p.obs)
    (s : State d) (h : (setLeaf p x s).2 = false) :
    read? q (setLeaf p x s).1 = read? q s := by
  -- slide-step
  rw [failed_write_leaves_state p x s h]
