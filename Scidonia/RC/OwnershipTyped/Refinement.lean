/-
The refinement: the two semantics of one λPure term agree, the fragment's
evaluation is total, an admitted program's result is a quotation of an
observation, and the sealed runner's `IO` description is the `pure` return of
that value.

The *copying* side of every statement here is the existing
`Scidonia.RC.StepStar`/`Value` of `Scidonia.RC.Pure` — the source calculus's own
reduction, whose write is the functional `slotUpdate`. The *direct* side is the
sealed runner of `Scidonia.RC.OwnershipTyped.Executor`. The two are related at
the value the same term's reduction reaches, and `stepStar_value_unique` is what
puts the two paths together: the reduction is deterministic, so a value a path
ends at is the only value any path from that term ends at.

The closedness hypothesis of the statements is part of the obligation — the
client submits a closed program — and not something the agreement needs: the
copying reduction is deterministic and the evaluation's environment agreement is
carried by `WF`. The statements keep it because that is the obligation.
-/
import Scidonia.RC.OwnershipTyped.Executor

namespace Scidonia.RC

namespace OwnershipTyped

open Scidonia.FracPerm.StateVar (Slot)
open Scidonia.FracPerm.StateVar.Layout5 (ObsDesc)

/-- A value does not step, so every path from it is the empty one. -/
theorem stepStar_of_value {a c : Expr} (hv : Value a) (h : StepStar a c) : a = c := by
  induction h with
  | refl _ => rfl
  | step hs _ _ => exact (value_no_step hs hv).elim

/-- A value a path ends at is the only value any path from the same term ends at:
the source reduction is deterministic, and a value does not step, so no path
leaves the value it reaches. -/
theorem stepStar_value_unique : ∀ {a b : Expr}, StepStar a b → Value b →
    ∀ {c : Expr}, StepStar a c → Value c → b = c := by
  intro a b h₁
  induction h₁ with
  | refl _ =>
      intro hv c h₂ hw
      exact stepStar_of_value hv h₂
  | step hs _ ih =>
      intro hv c h₂ hw
      cases h₂ with
      | refl _ => exact (value_no_step hs hw).elim
      | step hs₂ h₂' =>
          obtain rfl := step_deterministic hs hs₂
          exact ih hv h₂' hw

/-- The agreement: an admitted, closed program of the fragment evaluated by the
sealed runner reaches exactly the value the copying λPure reduction of the *same*
term reaches. The reduction hypothesis is a statement about the existing
`Scidonia.RC.StepStar`, and `evalArray` is the direct side's evaluation. -/
theorem evalArray_sound {o : ObsDesc} {e v : Expr}
    (h : Own (TyEnv.empty : TyEnv) .none e (.obs o)) (_hc : Closed e)
    (hs : StepStar e v) (hv : Value v) : evalArray e = some v := by
  obtain ⟨w, arr', hrun, hstep, hval, _, _⟩ :=
    runOn_simulate (Γ := TyEnv.empty) (κ := .none) (τ := .obs o) (arr := #[]) h
      WF.empty Inv.none
  rw [inst_none] at hstep
  have hwv : w = v := stepStar_value_unique hstep hval hs hv
  rw [evalArray_eq_runOn, hrun, hwv]
  rfl

/-- Totality: every admitted, closed program of the fragment terminates — the
sealed runner's evaluation reaches a λPure value, and the copying reduction
reaches that same value. -/
theorem evalArray_total {o : ObsDesc} {e : Expr}
    (h : Own (TyEnv.empty : TyEnv) .none e (.obs o)) (_hc : Closed e) :
    ∃ v, StepStar e v ∧ Value v ∧ evalArray e = some v := by
  obtain ⟨w, arr', hrun, hstep, hval, _, _⟩ :=
    runOn_simulate (Γ := TyEnv.empty) (κ := .none) (τ := .obs o) (arr := #[]) h
      WF.empty Inv.none
  refine ⟨w, ?_, hval, ?_⟩
  · rw [inst_none] at hstep
    exact hstep
  · rw [evalArray_eq_runOn, hrun]
    rfl

/-- The quotation lemma: an admitted program's result is an observation value and
carries no unary root node, so the protected cell is never among the values the
sealed runner returns. -/
theorem evalArray_no_root {o : ObsDesc} {e : Expr}
    (h : Own (TyEnv.empty : TyEnv) .none e (.obs o)) {v : Expr}
    (hav : evalArray e = some v) : hasRoot v = false := by
  obtain ⟨w, arr', hrun, _, _, hobs, _⟩ :=
    runOn_simulate (Γ := TyEnv.empty) (κ := .none) (τ := .obs o) (arr := #[]) h
      WF.empty Inv.none
  have hwv : w = v := by
    have hmap := hav
    rw [evalArray_eq_runOn, hrun] at hmap
    simp only [Option.map_some] at hmap
    exact Option.some.inj hmap
  rw [← hwv]
  exact hobs o rfl

/-- The sealed runner's logical `IO` equation: under the same hypotheses the
runner is the `pure` return of the value the copying reduction reaches. This is
an equality of Lean `IO` *descriptions* — the runner's single `return` — and not
a kernel statement about executing `IO`, about a foreign backend or about a
physical address. -/
theorem runFresh_eq_pure {o : ObsDesc} {e v : Expr}
    (h : Own (TyEnv.empty : TyEnv) .none e (.obs o)) (hc : Closed e)
    (hs : StepStar e v) (hv : Value v) : runFresh e h = pure v :=
  runFresh_of_evalArray h (evalArray_sound h hc hs hv)

end OwnershipTyped

end Scidonia.RC
