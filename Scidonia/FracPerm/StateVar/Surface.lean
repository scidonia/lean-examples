/-
The generic structured recipes: the command trees of a state variable, with no
state in them.

`RTree` is a read recipe: observe an operation's result and continue. `PTree` is
a program recipe: write and continue with whether the write took effect, or run
a read tree as a read phase and continue with its result. Both are indexed by
the type of the value they compute, and a fork's branches keep their own
(result) types, exactly as the structured interface's `RTree`/`PTree` do
(`Scidonia/FracPerm/Structured/Surface.lean`).

Neither tree mentions a state, a share, a fraction, a ledger or a heap: the
operations are the only connection to a `LawfulStateVar`, and the semantics
belongs to `Scidonia.FracPerm.StateVar.Model`. The trees are parameterised by
the operation types and the result family themselves, so that a tree can be
written without naming a state; where a `LawfulStateVar` is in scope,
`Model.lean`'s `RT` and `PT` write `RTree α` and `PTree α` with only the result
type named.

This module is the generic counterpart of the structured interface's surface and
nothing more. It adds no runner: there is no sealed `Reader`/`Program` and no
new backend, and the array instance's trees are recipes for the *existing*
`runFresh` interpreter, translated by `Scidonia.FracPerm.StateVar.Array`. -/
import Scidonia.FracPerm.StateVar.Class

namespace Scidonia.FracPerm.StateVar

/-- A read recipe: a value, an observation with its continuation, or a fork.

* `pure a` observes nothing and returns `a`.
* `read o k` observes operation `o` and continues with `k` applied to what it
  observed. The continuation's argument type is the operation's `Result`, so a
  read tree cannot be handed a value belonging to a different operation.
* `fork l r k` is a fork: `l` and `r` are branches, and `k` is applied to the
  pair of their results once both have finished. The branches' result types are
  the constructor's own implicit arguments, so this is an indexed family rather
  than a parameterised one. -/
inductive RTree (ReadOp : Type) (Result : ReadOp → Type) : Type → Type 1 where
  | pure {α : Type} (a : α) : RTree ReadOp Result α
  | read {α : Type} (o : ReadOp) (k : Result o → RTree ReadOp Result α) :
      RTree ReadOp Result α
  | fork {α β γ : Type} (l : RTree ReadOp Result β) (r : RTree ReadOp Result γ)
      (k : β × γ → RTree ReadOp Result α) : RTree ReadOp Result α

/-- A program recipe: a value, a write with its continuation, or a read phase.

* `pure a` returns `a`.
* `write w k` performs the write `w` and continues with `k` applied to whether
  it took effect.
* `phase r k` runs the read tree `r` as a read phase and continues with `k`
  applied to its result. While `r` runs, no write step exists; that is a
  property of the semantics in `Model.lean`, not of this type. -/
inductive PTree (ReadOp : Type) (Result : ReadOp → Type) (WriteOp : Type) :
    Type → Type 1 where
  | pure {α : Type} (a : α) : PTree ReadOp Result WriteOp α
  | write {α : Type} (w : WriteOp) (k : Bool → PTree ReadOp Result WriteOp α) :
      PTree ReadOp Result WriteOp α
  | phase {α β : Type} (r : RTree ReadOp Result β)
      (k : β → PTree ReadOp Result WriteOp α) : PTree ReadOp Result WriteOp α

section
variable {ReadOp : Type} {Result : ReadOp → Type} {WriteOp : Type} {α β : Type}

/-- Sequence two read recipes: run the first, then apply the continuation to
its result. Structural on the first tree. -/
def RTree.bind : RTree ReadOp Result α → (α → RTree ReadOp Result β) →
    RTree ReadOp Result β
  | .pure a, f => f a
  | .read o k, f => .read o (fun o' => (k o').bind f)
  | .fork l r k, f => .fork l r (fun p => (k p).bind f)

/-- Sequence two program recipes; as `RTree.bind`. -/
def PTree.bind : PTree ReadOp Result WriteOp α →
    (α → PTree ReadOp Result WriteOp β) → PTree ReadOp Result WriteOp β
  | .pure a, f => f a
  | .write w k, f => .write w (fun b => (k b).bind f)
  | .phase r k, f => .phase r (fun a => (k a).bind f)

end

end Scidonia.FracPerm.StateVar
