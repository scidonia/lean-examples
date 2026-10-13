/-
The sealed runner of the ownership-typed fragment: the one place that holds a
protected cell.

`exec` is the fragment's evaluation — `Scidonia.RC.OwnershipTyped.runWith` — at
the sealed executor's own write step, which puts the exclusivity check of
`Scidonia.FracPerm.assertExclusiveArray` in front of the update. It is private
here, so no client can name it, and no public function of the sealed executor
accepts an array: `evalArray` creates the session's cell itself and returns only
the quoted observation, and `runFresh` is the `IO` runner over it. The model's
own evaluator, `Scidonia.RC.OwnershipTyped.runOn`, is public and pure — it takes
the array from the caller, it is what the theorems are stated about, and it is
not a route to a session's array.

The check in front of the update is the identity in the logic
(`exec_eq_runOn`), so the shipped runner computes what the model computes.
Whether an update happens *in place* is not part of that statement: it is
run-time evidence from `ScidoniaInPlace`, and it is not claimed here.
-/
import Scidonia.RC.OwnershipTyped.Model
import Scidonia.FracPerm.InPlace

namespace Scidonia.RC

namespace OwnershipTyped

open Scidonia.FracPerm.StateVar (Slot)
open Scidonia.FracPerm.StateVar.Layout5 (ObsDesc)

/-- The sealed executor's update step: the exclusivity check, which is the
identity in the logic, in front of the in-place write. Under
`SCIDONIA_CHECK_INPLACE=1` an array that is not exclusively owned makes the
update loud instead of quietly copying it, which is what the check is for. -/
private def sealedWrite (a : Array Slot) (t : Slot) : Array Slot :=
  (Scidonia.FracPerm.assertExclusiveArray "Scidonia.RC.OwnershipTyped.write" a).set! 0 t

/-- The sealed interpreter: the fragment's evaluation, owning the one element
array and updating it in place. It is private, so no client can name it. -/
private def exec (ρ : VEnv) (arr : Array Slot) (e : Expr) : Option (Expr × Array Slot) :=
  runWith sealedWrite ρ arr e

/-- The sealed interpreter is the model's recursion: its one difference is the
exclusivity check in front of each update, which is the identity in the logic,
so in the logic it threads the same array and computes the same value. -/
private theorem exec_eq_runOn (ρ : VEnv) (arr : Array Slot) (e : Expr) :
    exec ρ arr e = runOn ρ arr e :=
  runWith_congr
    (fun a t => by simp [sealedWrite, Scidonia.FracPerm.assertExclusiveArray]) e ρ arr

/-- The value-level evaluation of an admitted program: the sealed interpreter run
on the fresh cell it creates, returning only the quoted observation. The array is
created here and never leaves this function, and the result is an `Expr` and
nothing else. -/
def evalArray (e : Expr) : Option Expr := (exec (fun _ => none) #[] e).map (fun p => p.1)

/-- The shipped runner is the model's recursion at the fresh cell, so the
theorems — which are stated about that recursion — are statements about the
shipped runner. -/
theorem evalArray_eq_runOn (e : Expr) :
    evalArray e = (runOn (fun _ => none) #[] e).map (fun p => p.1) := by
  simp only [evalArray, exec_eq_runOn]

/-- Run an admitted program in a fresh protected session: the interpreter creates
the cell internally and returns only the quoted observation. A program the
discipline does not admit fails the action rather than returning a value, which
is a failure the totality theorem makes unreachable for an admitted one. -/
def runFresh {o : ObsDesc} (e : Expr) (_ : Own (TyEnv.empty : TyEnv) .none e (.obs o)) :
    IO Expr := do
  match exec (fun _ => none) #[] e with
  | some (v, _) => return v
  | none =>
      throw (IO.userError "Scidonia.RC.OwnershipTyped.runFresh: the program did not evaluate")

/-- The runner's single `return`: under the value-level evaluation the runner is
the `pure` return of that value, which is the equation the `IO` description is
read at. -/
theorem runFresh_of_evalArray {o : ObsDesc} {e v : Expr}
    (h : Own (TyEnv.empty : TyEnv) .none e (.obs o)) (hav : evalArray e = some v) :
    runFresh e h = pure v := by
  have hmap : (exec (fun _ => none) #[] e).map (fun p => p.1) = some v := by
    simpa only [evalArray] using hav
  match hexec : exec (fun _ => none) #[] e with
  | none =>
      rw [hexec] at hmap
      simp at hmap
  | some p =>
      obtain ⟨vp, ap⟩ := p
      rw [hexec] at hmap
      have hvp : vp = v := by simpa using hmap
      simp only [runFresh, hexec]
      rw [hvp]

end OwnershipTyped

end Scidonia.RC
