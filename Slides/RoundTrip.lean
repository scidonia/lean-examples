import Scidonia.FracPerm

open Scidonia.FracPerm HSt

/-- Take out half, read with it, return it, then write. -/
def roundTrip :=
  acquire (σ := Array Nat) 0 (1 / 2) >>>= fun t =>
  read t 0 >>>= fun v =>
  release t >>>= fun _ =>
  write (0, 7) >>>= fun _ => ret v

/-- The precondition `bind` composes for `roundTrip` holds at the empty
ledger: the verification condition `exec` asks for. -/
theorem roundTrip_pre (a : Array Nat) : HSt.pre roundTrip [] a := by
  -- slide-step
  simp only [HSt.pre]
  -- slide-step
  simp [Ledger.held]
  -- slide-step
  grind
