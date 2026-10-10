import Scidonia.FracPerm

open Scidonia.FracPerm.StateVar

/-- No element of any description encodes to a reference: one proof, by
induction on the description, for every datatype the universe describes. -/
theorem noRef_every (ℓ : Loc) (d : Desc) : ∀ x : El d, NoRef ℓ (encodeEl d x) := by
  -- slide-step
  induction d
  -- slide-step
  case unit => intro x; trivial
  -- slide-step
  case nat => intro x; trivial
  -- slide-step
  case sum a b iha ihb => exact fun | .inl x => iha x | .inr y => ihb y
