/-
A structured interface over fractional permissions: a read-only `Reader` and an
exclusive `Program`, sealed, with a notional fork/join `parallel` whose shipped
executor runs the branches one after the other.

`Scidonia.FracPerm` makes the fractional bookkeeping a client's business: a
program holds a ledger, borrows a fraction with `acquire`, reads with the token
that names the fraction, gives it back with `release`, and `exec` demands a
proof that the whole state is held at the end. This module draws the same
accounting from the shape of the program instead. A program enters a read phase
with `Program.readPhase`, runs a tree of `Reader` computations, joins every
branch, and writes with `Program.set` only outside a read phase.

The fractions are not gone; they are internal. Every active read branch carries
a share of the same array, the root read phase carries `1`, a fork gives each
child half its parent's share, and a join restores the parent's share once both
children have stopped. `Scidonia.FracPerm.Structured.Model` states and proves
that invariant over the command trees this module builds. No client value names
a fraction, a ghost id, a ledger, or a closing proof, because no client
operation takes or returns one.

The surface:

* `Reader α` is a read-only computation, `Program α` a computation that owns
  the object. Both are monads, so ordinary `do` notation works.
* `Reader.get i` yields `some (a[i])` or `none`, `Reader.size` the array's
  size, and `Reader.parallel l r` runs `l` and `r` as two branches that join to
  a pair.
* `Program.readPhase r` runs a reader tree as a read phase against the array,
  and `Program.set i v` writes the element at `i`, yielding `false` and leaving
  the array unchanged when `i` is out of bounds.
* `runFresh init p` is the only way to run a program against a session's array:
  it creates that array internally from `init` (a size and a fill value) and
  returns the program's result. The array never leaves the executor, and no
  public route reaches it. `Model.run`/`val`/`pval` are the model's pure
  denotation — public, and what the theorems are stated about — and they
  evaluate a command tree on an array the *caller* supplies; they reach no
  session's array.

What a client cannot do, and why that is the point:

* There is no write in `Reader`, so a read phase cannot touch the array.
* There is no `liftIO`, no spawn, no task handle and no raw-state import or
  export, so no protected computation escapes the executor's control.
* There is no failure primitive, and failure is not modelled: no operation here
  fails, so failure semantics are out of scope rather than specified, and a real
  backend would have to add them at the executor. There is no liveness guarantee
  either — a continuation is an arbitrary pure Lean function of observations and
  may not terminate (a `partial` one can loop), and the model says nothing about
  a read phase that never finishes.
* A reader's continuation may be an arbitrary pure Lean function of the
  observations (`Option UInt64`, `Nat`, `Bool` and pairs built from them), and
  may return closures over them. It cannot capture the array, because no
  operation makes the array available.

`parallel` is notional. Its *semantics* is fork/join — `Model.lean` gives the
small-step relation and proves that any interleaving of the two branches
computes what the sequential strategy computes — and the shipped executor runs
the left branch and then the right one. A real concurrent backend is not
implemented here, and the reason it needs more than permissions is measured on
this toolchain: a run-time-built array captured by a `Task.spawn` closure
answers `false` to `isExclusiveUnsafe` once the task has been joined — the
object is marked as shared between threads, and `lean_is_exclusive` then
refuses it for the rest of its life — and the next `set!` returns an array at a
different address, a copy, while the same write on an untasked array keeps the
address. A backend that spawns tasks therefore has to get the array back to a
single owner, out of the task machinery's reach, before `set` can be in place;
the permission discipline alone does not do that.

## Sealing

`Reader` and `Program` hold a command tree behind a private constructor and a
private field. The generated eliminators (`Reader.casesOn`, `Reader.rec` and
their `Program` counterparts) are public, and `Reader.treeOf`/`Program.treeOf`
are public as well, so a command tree is reachable from a program. That is
harmless, and deliberately so: a tree holds no state. Its leaves are the
client's own pure continuations, and its nodes are a read index, a write index
and value, and a fork — `RTree`/`PTree` below mention no array, no fraction and
no ledger, and no operation of this interface produces the array or a function
of it. The state itself is created inside `Executor.runFresh`, threaded only by
the private interpreter there, and dropped when the program returns; a client
that writes its own interpreter over a tree it obtained can only run that
recipe against an array it makes itself, which is exactly what its own tree is
a recipe for. `Model.run`/`val`/`pval` are that interpreter, written once in
the model and public: they take the array from the caller, which is what the
theorems are stated about, and they are not a route to any session's array.

The routes that are closed:

* `Reader.mk` and `Program.mk` are private, so a client cannot forge a program
  from a tree it built or from a tree the eliminators exposed — rejected with
  "Constructor for `Scidonia.FracPerm.Structured.Program` is marked as
  private".
* `Reader.tree` and `Program.tree` are private fields, so `p.tree` is rejected
  with "Field `tree` from structure ... is private".
* The interpreter that takes the array (`Scidonia.FracPerm.Structured.execP`)
  is private to `Executor.lean`, so no client can call it by name, and no
  public function of the sealed executor accepts an array: `runFresh` takes an
  `Init`, which describes scalars only.

So the promise is: `runFresh` is the only runner of the sealed executor, and no
public route reaches the array a `runFresh` session creates. `pval` and `val`
evaluate a command tree on an array the caller supplies, which grants nothing
over a session's array — a client that has a tree already has a recipe, and one
that has no tree has nothing to evaluate.

A capability such as `HSt`'s would add nothing here: Lean privacy is per
module, so a private capability would keep the executor's own module out of the
tree as well, and the exposure above is already the harmless one.
-/
namespace Scidonia.FracPerm.Structured

/-- A read-only computation's command tree.

* `pure a` observes nothing and returns `a`.
* `get i k` observes `a[i]?` and continues with `k` applied to it.
* `size k` observes the array's size and continues with `k` applied to it.
* `fork l r k` is a fork: `l` and `r` are two branches of the current read
  phase, and `k` is applied to the pair of their results once both have
  finished.

The branches' result types are the constructor's own implicit arguments, which
is why this type is an indexed family rather than a parameterised one: a fork
of two branches of different result types is a tree whose own result type says
nothing about theirs.

`Scidonia.FracPerm.Structured.Model` gives this tree its small-step semantics:
the shares belong to the semantics, not to the tree, and this type mentions no
fraction, no array and no ledger. -/
inductive RTree : Type → Type 1 where
  | pure {α : Type} (a : α) : RTree α
  | get {α : Type} (i : Nat) (k : Option UInt64 → RTree α) : RTree α
  | size {α : Type} (k : Nat → RTree α) : RTree α
  | fork {α β γ : Type} (l : RTree β) (r : RTree γ)
      (k : β × γ → RTree α) : RTree α

/-- A program's command tree.

* `pure a` returns `a`.
* `set i v k` writes `v` at `i`. The write only happens outside a read phase;
  `k` is applied to whether the index was in bounds, and an out-of-bounds index
  leaves the array unchanged.
* `phase r k` runs the reader tree `r` as a read phase and continues with `k`
  applied to its result. While `r` runs, no `set` step exists: that is a
  property of the semantics in `Model.lean`, not of this type. -/
inductive PTree : Type → Type 1 where
  | pure {α : Type} (a : α) : PTree α
  | set {α : Type} (i : Nat) (v : UInt64) (k : Bool → PTree α) : PTree α
  | phase {α β : Type} (r : RTree β) (k : β → PTree α) : PTree α

/-- Sequence two trees: run the first, then apply the continuation to its
result. Structural on the first tree; the continuation is an ordinary Lean
function, applied to a value. -/
def RTree.bind : RTree α → (α → RTree β) → RTree β
  | .pure a, f => f a
  | .get i k, f => .get i (fun o => (k o).bind f)
  | .size k, f => .size (fun n => (k n).bind f)
  | .fork l r k, f => .fork l r (fun p => (k p).bind f)

/-- Sequence a program with a continuation; as `RTree.bind`. -/
def PTree.bind : PTree α → (α → PTree β) → PTree β
  | .pure a, f => f a
  | .set i v k, f => .set i v (fun b => (k b).bind f)
  | .phase r k, f => .phase r (fun a => (k a).bind f)

/-- A read-only computation: a command tree behind a private constructor and a
private field.

The constructor is private, so a client cannot build a `Reader`; the field is
private, so a client cannot project one; see the module note on sealing for
what the eliminators expose and why that is harmless. -/
structure Reader (α : Type) where
  private mk ::
  private tree : RTree α

/-- A computation that owns the object: as `Reader`, for `PTree`. -/
structure Program (α : Type) where
  private mk ::
  private tree : PTree α

namespace Reader

/-- The computation that returns `a` and observes nothing. -/
def pure (a : α) : Reader α := ⟨.pure a⟩

/-- Run `f` on `m`'s result. The continuation is an ordinary pure function of
the result; the two trees are sequenced. -/
def bind (m : Reader α) (f : α → Reader β) : Reader β :=
  ⟨m.tree.bind (fun a => (f a).tree)⟩

instance : Monad Reader where
  pure := pure
  bind := bind

/-- Observe the element at `i`, or `none` when `i` is out of bounds.

The continuation then receives an `Option UInt64`, a value detached from the
array: nothing in this interface can name the array itself. -/
def get (i : Nat) : Reader (Option UInt64) := ⟨.get i (fun o => .pure o)⟩

/-- Observe the array's size. -/
def size : Reader Nat := ⟨.size (fun n => .pure n)⟩

/-- Fork: `l` and `r` are two branches of the current read phase, and the pair
of their results is this computation's result.

Semantically the shares of the current phase are split between the branches and
restored when both have finished, which is what lets the branches run in either
order or at the same time; the shipped executor runs `l` and then `r`. -/
def parallel (l : Reader α) (r : Reader β) : Reader (α × β) :=
  ⟨.fork l.tree r.tree (fun p => .pure p)⟩

/-- The command tree of a reader: reads, forks and pure continuations. This is
the interpreter's view of a computation, and the generated eliminators expose
the same value.

The tree carries no array, no fraction and no ledger — see the module note on
sealing — so reading it gives a client no way to reach the state. What a client
can do with it is evaluate it on an array of its own, which is what
`Scidonia.FracPerm.Structured.val`/`pval` do and all they do; that reaches no
session's array and grants nothing over one. -/
def treeOf (r : Reader α) : RTree α := r.tree

end Reader

namespace Program

/-- The program that returns `a`. -/
def pure (a : α) : Program α := ⟨.pure a⟩

/-- Run `f` on `m`'s result. -/
def bind (m : Program α) (f : α → Program β) : Program β :=
  ⟨m.tree.bind (fun a => (f a).tree)⟩

instance : Monad Program where
  pure := pure
  bind := bind

/-- Run a reader tree as a read phase and continue with its result.

While the phase runs, no write exists: `Model.lean`'s configurations make the
writer's authority zero for the whole subtree, and only a `run` of a `pure`
reader returns it. -/
def readPhase (r : Reader α) : Program α :=
  ⟨.phase r.tree (fun a => .pure a)⟩

/-- Write `v` at `i`, yielding whether the index was in bounds. An
out-of-bounds index leaves the array unchanged and yields `false`.

The write happens in place when the array is exclusively owned, which is what
the executor threads it for; `Scidonia.FracPerm.assertExclusiveArray` is what
makes a shared array loud instead, under `SCIDONIA_CHECK_INPLACE=1`. -/
def set (i : Nat) (v : UInt64) : Program Bool :=
  ⟨.set i v (fun b => .pure b)⟩

/-- The command tree of a program; as `Reader.treeOf`, and with the same
boundary: a tree can be evaluated on an array the caller supplies, by
`Scidonia.FracPerm.Structured.pval`, and reaches no session's array. -/
def treeOf (p : Program α) : PTree α := p.tree

end Program

/-- What a fresh session starts from: the array's size and the value every
element is filled with. It describes scalars only, so a client cannot hand the
executor an array of its own. -/
structure Init where
  /-- The number of elements of the array. -/
  size : Nat
  /-- The value every element is initialised with. -/
  fill : UInt64

end Scidonia.FracPerm.Structured
