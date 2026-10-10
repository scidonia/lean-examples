/-
Compile-time checks for the structured interface
`Scidonia.FracPerm.Structured`.

These live in the check library, so they see exactly what a client sees. The
interface's rules are of two kinds here:

* The protocol's rules are behavioural, so their control is a run. `runFresh`
  is an `IO` action — it creates the array — so a run is checked by `#eval`:
  `check` throws when the observed value is not the expected one, and a thrown
  error fails the elaboration of this module.
* The sealing rules are rules of the *surface*: no write in `Reader`, no
  forging a `Program` from a tree, no naming the executor, no applying a
  program or a reader to an array. Their checks are `#guard_msgs` around
  commands whose elaboration must fail, with the message pinned, so a check
  fails both when the command starts being accepted and when it starts failing
  for another reason. Each is paired with an affirmative control: the protocol
  checks above, and the two `rfl` theorems showing what the eliminators do
  expose.

`Scidonia.FracPerm.Structured.Model` carries the semantic statements: the
observations a reader makes are all it can see, the shares of a read phase are
conserved, no `set` step exists while a read phase runs, a `wait` becomes a
`run` only when both children have finished, a `set` preserves the array's size
and is in bounds exactly when it yields `true`, and every interleaving of a read
phase computes what the sequential denotation computes.
-/
import Scidonia.FracPerm

open Scidonia.FracPerm.Structured

/-! ## Running the protocol

`check` fails the build when a run's value is not the expected one. -/

/-- Fail the elaboration unless `observed` is `expected`. -/
def check {α : Type} [BEq α] [Repr α] (name : String) (expected observed : α) : IO Unit := do
  unless expected == observed do
    throw (IO.userError s!"{name}: expected {repr expected}, observed {repr observed}")

/-! ## Q1: the handoff's example -/

/-- Q1's program: write, a read phase with two parallel readers, write, and
return what the readers saw. -/
def q1Program : Program (Option UInt64 × Option UInt64) := do
  let _ ← Program.set 0 17
  let r ← Program.readPhase (Reader.parallel (Reader.get 0) (Reader.get 1))
  let _ ← Program.set 1 23
  return r

#eval do
  check "Q1 handoff example" (some 17, some 0)
    (← runFresh { size := 1024, fill := 0 } q1Program)

/-! ## Q2: nested parallel readers -/

/-- Q2's program: the two writes come first, so what the readers see does not
depend on the fill, and the fork of forks and the size observation are all in
one read phase. -/
def q2Program : Program ((Option UInt64 × Option UInt64) × (Option UInt64 × Nat)) := do
  let _ ← Program.set 0 1
  let _ ← Program.set 1 2
  Program.readPhase
    (Reader.parallel (Reader.parallel (Reader.get 0) (Reader.get 1))
      (Reader.parallel (Reader.get 2) Reader.size))

#eval do
  check "Q2 nested parallel readers" ((some 1, some 2), (some 0, 5))
    (← runFresh { size := 5, fill := 0 } q2Program)

/-! ## Q3: an out-of-bounds write -/

/-- Q3's program: write out of bounds, then read the index that was not
written and one that was left alone. -/
def q3Program : Program (Bool × Option UInt64 × Option UInt64) := do
  let w ← Program.set 9 99
  let absent ← Program.readPhase (Reader.get 9)
  let untouched ← Program.readPhase (Reader.get 0)
  return (w, absent, untouched)

#eval do
  check "Q3 out-of-bounds set" (false, none, some 7)
    (← runFresh { size := 4, fill := 7 } q3Program)

/-! ## Q4: two fresh sessions over one program description -/

/-- Q4's program: read, write, read again — so the first read of a session
shows what that session's array holds before the program touched it. -/
def q4Program : Program (Option UInt64 × Bool × Option UInt64) := do
  let before ← Program.readPhase (Reader.get 0)
  let w ← Program.set 0 42
  let after ← Program.readPhase (Reader.get 0)
  return (before, w, after)

/- The same description, run twice. If the sessions shared anything, the
second run's first read would be the first run's write. -/
#eval do
  check "Q4 first session" (some 11, true, some 42)
    (← runFresh { size := 4, fill := 11 } q4Program)
  check "Q4 second session is its own array" (some 11, true, some 42)
    (← runFresh { size := 4, fill := 11 } q4Program)

/-! ## Q5: a reader that returns a closure over an observation -/

/-- Q5's reader: it returns a function of an observation it made. The closure
captures an `Option UInt64` and a `Nat`, never the array. -/
def q5Reader : Reader (Nat → Nat) := do
  let a ← Reader.get 0
  let n ← Reader.size
  return fun k => (match a with | some v => v.toNat | none => n) + k

/-- Q5's program: write, take the closure out of the read phase, write again
(which must still be in place; see the `structured-closure` harness case), and
apply the closure. -/
def q5Program : Program (Nat × Bool) := do
  let _ ← Program.set 0 5
  let f ← Program.readPhase q5Reader
  let w ← Program.set 1 6
  return (f 37, w)

#eval do
  check "Q5 closure over an observation" (42, true)
    (← runFresh { size := 4, fill := 0 } q5Program)

/-! ## Q6: a write inside a reader is rejected

`Program.set` is a `Program`, and a `Reader` has no write, so the `do` block of
a reader cannot contain one. -/

/- Q6: a `set` inside a `Reader`'s `do` block. -/
/--
error: Type mismatch
  Program.set 0 1
has type
  Program Bool
but is expected to have type
  Reader ?m.1
-/
#guard_msgs in
example : Reader Nat := do
  let _ ← Program.set 0 1
  return 0

/-! ## Q7: no raw array, no forged runner, no private route

The field and the constructor of both types are private, the sealed executor's
array-taking interpreter is private to its module, and neither type is a
function that an array could be applied to. What the eliminators do expose — a
command tree — and what a client may legitimately do with it — evaluate it on an
array of its own with the model's `val`/`pval` — are checked affirmatively at
the end. -/

/- Q7a: `Program`'s tree is a private field. -/
/--
error: Field `tree` from structure `Scidonia.FracPerm.Structured.Program` is private
-/
#guard_msgs in
example (p : Program α) : PTree α := p.tree

/- Q7b: `Program` cannot be built from a tree. -/
/--
error: Invalid `⟨...⟩` notation: Constructor for `Scidonia.FracPerm.Structured.Program` is marked as private
-/
#guard_msgs in
example (t : PTree α) : Program α := ⟨t⟩

/- Q7c: the array-taking interpreter cannot be named. -/
/--
error: Unknown identifier `execP`
-/
#guard_msgs in
example (a : Array UInt64) (t : PTree α) : α := execP a t

/- Q7d: the eliminator exposes the tree, and the tree cannot be turned back
into a program, so the route ends here. -/
/--
error: Invalid `⟨...⟩` notation: Constructor for `Scidonia.FracPerm.Structured.Program` is marked as private
-/
#guard_msgs in
example (p : Program α) : Program α := Program.casesOn p (fun t => ⟨t⟩)

/- Q7e: a program is not a function of an array, so there is no forged runner
that hands a program the state. -/
/--
error: Function expected at
  p
but this term has type
  Program α

Note: Expected a function because this term is being applied to the argument
  a
-/
#guard_msgs in
example (p : Program α) (a : Array UInt64) : α := p a

/- Q7f: neither is a reader, so a reader cannot be run against the state
either. -/
/--
error: Function expected at
  r
but this term has type
  Reader α

Note: Expected a function because this term is being applied to the argument
  a
-/
#guard_msgs in
example (r : Reader α) (a : Array UInt64) : α := r a

/-- Q7's affirmative control: the eliminators expose a *recipe*. This is
exactly the `get` node the interface built — an index and a continuation over
an observation — and nothing in a tree names the array. -/
example : Reader.treeOf (Reader.get 3) = RTree.get 3 (fun o => .pure o) := rfl

/-- Q7's second affirmative control: a program's tree is a `PTree` over the
program's own result type, so what a client can reach through the eliminators
is a command tree and no state. -/
example (p : Program Bool) : PTree Bool := Program.treeOf p

/-- Q7's third affirmative control, the boundary itself: the model's evaluators
are public and pure, and they evaluate a command tree on an array the *caller*
supplies. Here a client evaluates a reader's tree on its own array. This is the
documented use of `val`/`pval`, it involves no session, and it is what the
sealing note means by a tree being a recipe. -/
example :
    pval #[1, 2, 3] (PTree.phase (Reader.treeOf (Reader.get 1)) (fun a => .pure a)) =
      some 2 := rfl

/- Q7's fourth affirmative control: the same for a program's tree, on another
array of the client's own, with the write the tree names happening on that
array. -/
#guard pval #[4, 5, 6] (Program.treeOf (Program.set 0 9)) == true
