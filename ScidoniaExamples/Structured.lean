import Scidonia.FracPerm

/-!
# The structured interface by example

`Scidonia.FracPerm.Structured` is the structured interface over the same
fractional permissions: a read-only `Reader`, an exclusive `Program`, and a
notional `Reader.parallel` whose shipped executor runs the left branch and then
the right one. The fractions are internal — the root read phase holds `1`, a
fork splits its share in half, a join puts it back — and a client writes none
of them, takes no token, and proves nothing to run a program.

A program is a `Program` value built from `Reader.get`, `Reader.size`,
`Reader.parallel`, `Program.readPhase`, `Program.set`, `pure` and `bind`, so
ordinary `do` notation works. It is run with `runFresh init p`, which creates
the array from `init` and returns the program's result; the array never leaves
the executor. `Scidonia.FracPerm.Structured.Model` is where the shares are
proved to be conserved, where exclusion is proved — a `set` step has no source
while a read phase runs — and where schedule independence is proved: every
interleaving of a read phase computes what the sequential executor computes.

Each section states a program, runs it, and pins what it returns. The runs are
`IO` actions — `runFresh` creates the array — so they are checked by `#eval`
with a local `check` that fails the elaboration when a value is not the
expected one, and each section's comment states the value a reader should see.
-/

open Scidonia.FracPerm.Structured

/-- Fail the elaboration unless `observed` is `expected`. -/
def check {α : Type} [BEq α] [Repr α] (name : String) (expected observed : α) : IO Unit := do
  unless expected == observed do
    throw (IO.userError s!"{name}: expected {repr expected}, observed {repr observed}")

/-! ## The handoff's example

Write, a read phase whose body is two parallel readers, write, and return the
pair the readers saw. The array is `Init 1024 0`: index `0` holds `17` when the
read phase runs and index `1` still holds the fill, so the readers see
`(some 17, some 0)`. -/

/-- The example from the handoff: the fractions are nowhere in it. -/
def handoffExample : Program (Option UInt64 × Option UInt64) := do
  let _ ← Program.set 0 17
  let (a, b) ← Program.readPhase (Reader.parallel (Reader.get 0) (Reader.get 1))
  let _ ← Program.set 1 23
  return (a, b)

#eval do
  check "handoff example" (some 17, some 0)
    (← runFresh { size := 1024, fill := 0 } handoffExample)

/-! ## A nested read phase

A read phase whose body forks twice: `(get 0) ∥ ((get 1) ∥ (get 2))`, plus the
size observed beside the first branch. The executor runs the whole tree one
branch at a time; the semantics allows any interleaving and proves they all
agree. The writes come first, so the values do not depend on the fill; the size
is `5`, observed after the two writes and two more reads. -/

/-- A fork of a fork, and a size observation beside it. -/
def nestedExample : Program ((Option UInt64 × Nat) × (Option UInt64 × Option UInt64)) := do
  let _ ← Program.set 0 1
  let _ ← Program.set 1 2
  let _ ← Program.set 2 3
  Program.readPhase
    (Reader.parallel (Reader.parallel (Reader.get 0) Reader.size)
      (Reader.parallel (Reader.get 1) (Reader.get 2)))

#eval do
  check "nested read phase" (((some 1), 5), (some 2, some 3))
    (← runFresh { size := 5, fill := 0 } nestedExample)

/-! ## A write out of bounds, and a fresh session

`Program.set` yields whether the index was in bounds, and an out-of-bounds
index leaves the array alone; reading that index afterwards proves it. Two runs
of the *same* program description against two fresh sessions give the same
result, because a description is a recipe and each session creates its own
array. -/

/-- A read, a write, and a read again: the first read shows what the session
held before the program touched it. -/
def freshExample : Program (Option UInt64 × Bool × Option UInt64 × Bool) := do
  let before ← Program.readPhase (Reader.get 0)
  let w ← Program.set 0 42
  let after ← Program.readPhase (Reader.get 0)
  let outOfBounds ← Program.set 9 0
  return (before, w, after, outOfBounds)

#eval do
  check "fresh session, first run" (some 11, true, some 42, false)
    (← runFresh { size := 4, fill := 11 } freshExample)
  check "fresh session, second run" (some 11, true, some 42, false)
    (← runFresh { size := 4, fill := 11 } freshExample)

/-! ## A reader that returns a closure

A reader's result may be any pure Lean value computed from its observations,
including a function of them. This one returns a closure over an
`Option UInt64` and a `Nat` and nothing else — no operation of the interface
makes the array available — and applying that closure after the read phase
behaves. -/

/-- A reader whose result is a function of what it observed. -/
def closureReader : Reader (Nat → Nat) := do
  let a ← Reader.get 0
  let n ← Reader.size
  return fun k => (match a with | some v => v.toNat | none => n) + k

/-- Write, take the closure out of the read phase, write again — the write
after the join is what the `structured-closure` harness case checks in place —
and apply the closure: `5 + 37`. -/
def closureExample : Program (Nat × Bool) := do
  let _ ← Program.set 0 5
  let f ← Program.readPhase closureReader
  let w ← Program.set 1 6
  return (f 37, w)

#eval do
  check "closure over an observation" (42, true)
    (← runFresh { size := 4, fill := 0 } closureExample)
