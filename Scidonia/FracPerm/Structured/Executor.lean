/-
The sequential executor of the structured interface: the one place that holds
the array.

`runFresh` creates the array from an `Init`, interprets the program's command
tree against it, and returns the program's result; the array never leaves this
module, and no public route reaches it. `execP` and `execR` do the interpreting
and are private here, so `runFresh` is the only runner of the sealed executor,
and no public function of the sealed executor accepts an array. The model's own
evaluators, `Model.val` and `Model.pval`, are public and pure: they take the
array from the caller, they are what the theorems are stated about, and they
are not a route to a session's array.

`Reader.parallel` is interpreted as left branch and then right branch. The
shares of `Scidonia.FracPerm.Structured.Model` are what say that this order is
not part of the meaning of a fork: they make every interleaving compute the
same value, so a sequential backend is a valid implementation of a parallel
semantics.

The array is threaded to keep it exclusively owned, which is what makes a
`set` an update in place rather than a copy:

* `execP` owns the array and passes it on. A `set` step hands it to
  `Scidonia.FracPerm.assertExclusiveArray` and then to `Array.set!`; the check
  is the identity in the logic and, under `SCIDONIA_CHECK_INPLACE=1`, makes a
  copy loud instead of silent.
* `execR` borrows the array (`@&`) and never keeps it: it only observes single
  elements and the size, and the continuations it applies receive those
  observations, never the array. A read phase therefore runs without taking a
  second reference.
* A read phase's branches are interpreted one after the other inside the single
  `execP` recursion, and the trees themselves are built before the array
  exists, so no closure holds it.

`nix develop -c lake exe inplace` checks the result at run time: the
`structured-unique` and `structured-closure` children run with the check armed
and exit zero, and the generated C is what shows the array reaching `set` with
one reference. -/
import Scidonia.FracPerm.Structured.Surface
import Scidonia.FracPerm.Structured.Model
import Scidonia.FracPerm.InPlace

namespace Scidonia.FracPerm.Structured

/-- Interpret a read tree against a borrowed array. The array is a `@&`
parameter, so the call takes no reference of its own, and nothing in this
function retains it: the observations handed to the continuations are an
`Option UInt64`, a `Nat` and a pair of branch results.

A fork is interpreted left branch and then right branch. -/
private def execR (a : @& Array UInt64) : RTree α → α
  | .pure x => x
  | .get i k => execR a (k a[i]?)
  | .size k => execR a (k a.size)
  | .fork l r k => execR a (k (execR a l, execR a r))

/-- Interpret a program tree, owning the array and passing it on.

A `set` step is the only step that touches the array: it checks exclusivity
first, updates in place, and continues with the updated array. An out-of-bounds
index is not a write at all — the array is passed on unchanged and the
continuation receives `false`.

A `phase` step runs the reader tree with the array borrowed and then continues
with the same owned array, so the phase costs no second reference. -/
private def execP (a : Array UInt64) : PTree α → α
  | .pure x => x
  | .set i v k =>
    if i < a.size then
      execP ((Scidonia.FracPerm.assertExclusiveArray
        "Scidonia.FracPerm.Structured.set" a).set! i v) (k true)
    else
      execP a (k false)
  | .phase r k => execP a (k (execR a r))

/-- Run a program against an array created here from `init`.

The array is a fresh `Array.replicate init.size init.fill` and is dropped when
the program returns; nothing in the result names it. There is no failure
primitive, so there is no failure handling to add here — and no liveness
guarantee either, since a continuation may not terminate. -/
def runFresh (init : Init) (p : Program α) : IO α := do
  let a : Array UInt64 := Array.replicate init.size init.fill
  return execP a p.treeOf

/-- The executor's read interpreter is the model's read denotation: the same
recursion, with the array borrowed. -/
private theorem execR_eq_val (a : @& Array UInt64) (t : RTree α) : execR a t = val a t := by
  induction t with
  | pure x => rfl
  | get i k ih => exact ih (a[i]?)
  | size k ih => exact ih a.size
  | fork l r k ihl ihr ihk =>
    show execR a (k (execR a l, execR a r)) = val a (k (val a l, val a r))
    rw [ihl, ihr]
    exact ihk (val a l, val a r)

/-- The executor's program interpreter is the model's program denotation. Its
one difference is that it hands the array to `assertExclusiveArray` before the
update, and that check is the identity in the logic, so in the logic it threads
the same array and computes the same value. -/
private theorem execP_eq_pval : ∀ (t : PTree α) (a : Array UInt64), execP a t = pval a t := by
  intro t
  induction t with
  | pure x => intro a; rfl
  | set i v k ih =>
    intro a
    by_cases h : i < a.size
    · simp only [execP, pval, ite_eq_left h]
      exact ih true (a.set! i v)
    · simp only [execP, pval, ite_eq_right h]
      exact ih false a
  | phase r k ih =>
    intro a
    simp only [execP, pval]
    rw [execR_eq_val]
    exact ih (val a r) a

/-- `runFresh` computes the model's denotation of the program against the array
it created: the shipped interpreter is the model's recursion, and the in-place
check in front of each update is the identity in the logic. Whether the update
happens in place is not part of this statement; it is run-time evidence from
`ScidoniaInPlace`. -/
theorem runFresh_eq_pval (init : Init) (p : Program α) :
    runFresh init p = (do
      let a : Array UInt64 := Array.replicate init.size init.fill
      return pval a p.treeOf) := by
  simp only [runFresh, execP_eq_pval]

end Scidonia.FracPerm.Structured
