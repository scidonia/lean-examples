/-
The in-place check of `Scidonia.FracPerm` exercised as a running program.

A proved specification cannot see whether a `write` updated its object in
place or replaced it with a copy: `assertExclusive` is the identity in the
logic. This program observes the difference at run time, through the pointer
and the reference count of the object the interface actually threads.

Run it with `lake exe inplace`; it exits `0` only when every case below holds,
and each case that fails names what it expected and what it saw. It must run
with the check off — it runs the shared and the literal case itself, and those
must copy — and the child processes are what carry
`SCIDONIA_CHECK_INPLACE=1`. The cases:

* a uniquely owned array — built by pushing at run time, so no compiler
  optimization can share it with a second expression — run through two
  programs that write and read through fractional permissions. The array must
  be exclusively owned before the run, must live at the same address after it,
  and must hold the values the program wrote.
* the same program on an array with a live second reference. The write must
  copy: the addresses differ and the original keeps its values. This is the
  control that shows the check's detector answers "not exclusively owned"
  when there really is a second reference, rather than never saying so.
* a literal array, `#[10, 11, 12, 13]`, which the compiler emits once as a
  persistent object, so it is never exclusively owned and a write to it always
  copies. Its value is chosen at run time so that the compiler cannot fold the
  whole case away.
* the counter: a structure whose mutable state is a count and an array
  field. Written in place, the structure and the log keep their addresses.
  With a live reference to the log held outside the structure, `record` copies
  the log — its address changes and the outside reference keeps its values —
  while the structure itself is still updated in place.
* the structured interface's `structured-unique` and `structured-closure`
  programs, run through `Scidonia.FracPerm.Structured.runFresh`, whose array is
  created inside the executor; the value assertions are all the parent can see
  of the array. Their checked children exit zero, which is what shows that
  every `set` of those programs updated in place.
* the path writes of `Scidonia.FracPerm.StateVar.Layout5` on an
  `Array (UInt64 × UInt64)` and on an `Array (Array UInt64)`: an owned
  `Array.swapAt` take-out that leaves the layout's placeholder in the slot, and
  its inverse put-back, must leave the array's buffer and the sampled sibling
  struct (the one each case names) at the same address, and the value at the
  path must be the one written while a sibling's stays fixed. The update is fused over the
  path and returns the state alone, so the compiler reuses the struct cell at
  the written index: that cell keeps its address when it is exclusively owned
  and changes when a live second reference reaches it, and both are asserted.
  Where the focused element is itself an array its own address is the same
  measurement: unchanged when the element is exclusively owned, and changed when
  a live reference to it is held, because then the write inside it copies it.
* the sealed write of `Scidonia.FracPerm.StateVar.SealedStateVar` on the shipped
  `Array (UInt64 × UInt64)` instance. That class supplies the layout and the
  equality and no code, so the write is `Layout5.setLeaf` through the cast in
  `rep`; the instance's `rep` is `rfl`, so the cast erases. `sealed-unique`
  measures what `layout5-unique` measures — the array's buffer and the struct at
  the written index both keep their addresses, the write landed, and a sibling
  slot is unchanged — and `sealed-checked-unique` is the same write in a child
  with `SCIDONIA_CHECK_INPLACE=1`, which must report the check enabled and exit
  zero.
* child processes launched as `lake exe inplace unique|shared|counter-…` with
  `SCIDONIA_CHECK_INPLACE=1`. The shared cases must exit nonzero with the
  write site named on standard error, the unique cases must exit zero having
  reported the check enabled, which is what shows the check was armed and did
  not fire on an update in place. The counter's `bump` writes only `hits`, so
  the child that bumps a counter with a shared log must exit zero too: the
  counter's check is told the operation, and an abort must mean that this
  write is about to copy, not merely that some part of the object is shared.
  `layout5-unique` and `layout5-nest` are path writes with the check armed —
  the array and the focused element are exclusively owned, so neither check
  must report anything — while `layout5-shared` (a live reference to the array)
  and `layout5-nest-shared` (a live reference to the focused element) must end
  the process naming the `Layout5` site of the array and of the element
  respectively.
* the updates of `ScidoniaExamples.Updates`: a flat array (`arrSet`, the
  primitive), a nested array (`nestedSet`, a two-step path write through the
  sealed class) and a struct tree of depth four (`treeSet`, a path write of
  depth four through the sealed class). Each case observes the addresses the
  update is about — the flat array's buffer, the nested array's outer buffer
  and focused inner array, and the tree's spine cells down the written path —
  with the same `addressIO` instrument the path-write cases use. The unique
  case asserts the addresses are kept, and the aliased case holds a live second
  reference and asserts they change, which is the copy. Their checked children
  run the unique writes with `SCIDONIA_CHECK_INPLACE=1` and must exit zero.
* the union-find of `ScidoniaExamples.UnionFind`, whose writes are that sealed
  class's take-out update on a flat `Array UInt64`: `uf-unique` runs the
  disciplined shape and asserts both buffers kept their addresses and that the
  unions left the partition the schedule names, `uf-shared` runs the same unions
  with a live second reference to both arrays and asserts both addresses changed
  — the copies — that the reference the writes did not go through still reads the
  arrays the run started from, and the same partition. `uf-checked-shared` is the
  aliased shape in a child with the check armed, which must end the process
  naming the `Layout5` *array* site, because that is the write about to copy.
  `uf-checked-focus` is the disciplined shape in a child with the check armed,
  and it is the one case here that does not exit zero: an element of an
  `Array UInt64` is a machine word and not a heap object, `isExclusiveUnsafe`
  answers `false` for it, and the library's focus guard therefore stops that child
  at the focus site — where no copy would happen, as `uf-unique`'s addresses show.
  The case pins that pair of facts instead of a zero exit, so a change in either
  fails the run.
* the benchmark of those updates and of the union-find: `bench-array`,
  `bench-tree` and `bench-union-find` print the measured nanoseconds per update
  (per union) for the exclusive and the aliased shape, at increasing array sizes,
  tree depths and element counts, with the address relation an untimed probe of
  each shape observed. The numbers are printed rather than asserted, and what
  they measure is a run of this program on this toolchain.
-/
import Scidonia.FracPerm
import ScidoniaExamples.Updates
import ScidoniaExamples.UnionFind

open Scidonia.FracPerm
open Scidonia.FracPerm.StateVar
open Scidonia.FracPerm.HSt
open ScidoniaExamples.Updates
open ScidoniaExamples.UnionFind

/-! ## The programs

Two array programs in the shape the interface's own checks use: one write, a
read lent out under a token, the fraction returned, and a second write; and
one write, three readers holding `1/2`, `1/4` and `1/4` at once, and a second
write. Then a counter program, and the counter's bump alone. -/

/-- The P1 program: write, lend out a third and two thirds, read with the
third, give both back, and write again. -/
def p1 :=
  write (σ := Array Nat) (0, 7) >>>= fun _ =>
  acquire 0 (1 / 3) >>>= fun t₁ =>
  acquire 1 (2 / 3) >>>= fun t₂ =>
  read t₁ 0 >>>= fun v =>
  release t₁ >>>= fun _ =>
  release t₂ >>>= fun _ =>
  write (1, 9) >>>= fun _ =>
  ret v

/-- The readers program: write, lend out a half and two quarters, read with
each token, give all three back, and write again. -/
def p2 :=
  write (σ := Array Nat) (0, 1) >>>= fun _ =>
  acquire 0 (1 / 2) >>>= fun t₁ =>
  acquire 1 (1 / 4) >>>= fun t₂ =>
  acquire 2 (1 / 4) >>>= fun t₃ =>
  read t₁ 1 >>>= fun v₁ =>
  read t₂ 2 >>>= fun v₂ =>
  read t₃ 3 >>>= fun v₃ =>
  release t₁ >>>= fun _ =>
  release t₂ >>>= fun _ =>
  release t₃ >>>= fun _ =>
  write (1, 2) >>>= fun _ =>
  ret (v₁, v₂, v₃)

/-- The counter program: bump, lend out a third, read the log's first entry
with it, give the fraction back, record, and return the entry read. -/
def counterProg :=
  write (σ := Counter) Counter.WriteOp.bump >>>= fun _ =>
  acquire 0 (1 / 3) >>>= fun t =>
  read t (Counter.ReadOp.entry 0) >>>= fun v =>
  release t >>>= fun _ =>
  write (Counter.WriteOp.record 7) >>>= fun _ =>
  ret v

/-- The counter's bump alone: its one write touches `hits` and not the log. -/
def counterBumpProg :=
  write (σ := Counter) Counter.WriteOp.bump >>>= fun _ => ret ()

/-! ## Observing a run

`exclusive` and `address` read the object borrowed — the `@&` is what keeps
them from taking a reference of their own — so `exclusive` answers for the
caller's reference and the address is the object the program is handed. -/

/-- Whether `x` is exclusively owned: a single reference to a non-persistent
object. -/
def exclusive {α : Type} (x : @& α) : Bool := unsafe isExclusiveUnsafe x

/-- The address `x` lives at. -/
def address {α : Type} (x : @& α) : USize := unsafe ptrAddrUnsafe x

/-- What one run of an array program leaves to check: whether the array was
exclusively owned and where it lived before the run, where the program's array
lives after it, and what the program returned. -/
structure Run (β : Type) where
  /-- Whether the array handed to the program was exclusively owned. -/
  exclusiveBefore : Bool
  /-- The address the program's array lived at before the run. -/
  addressBefore : USize
  /-- The address the program's array lives at after the run. -/
  addressAfter : USize
  /-- What the program returned. -/
  value : β
  /-- The array the program left behind. -/
  array : Array Nat

/-- Run `prog` on `a` and observe it. `a` is consumed by the run, so a caller
that passes its only reference sees `exclusiveBefore` as `true`. -/
def observe {β : Type} {P : Pre (Array Nat)} {Q : Post (Array Nat) β}
    (prog : HSt (Array Nat) P β Q) (a : Array Nat) (hp : P [] a)
    (hq : ∀ b l' a', Q [] a b l' a' → l'.held = 1) : Run β :=
  let exclusiveBefore := exclusive a
  let addressBefore := address a
  let r := prog.exec a hp hq
  let addressAfter := address r.2
  { exclusiveBefore, addressBefore, addressAfter, value := r.1, array := r.2 }

/-- What one run of a counter program leaves to check: whether the counter was
exclusively owned and where it and its log lived before the run, where they
live after it, and what the program returned. -/
structure CounterRun (β : Type) where
  /-- Whether the counter handed to the program was exclusively owned. -/
  exclusiveBefore : Bool
  /-- The address the program's counter lived at before the run. -/
  structAddressBefore : USize
  /-- The address the program's counter lives at after the run. -/
  structAddressAfter : USize
  /-- The address the counter's log lived at before the run. -/
  logAddressBefore : USize
  /-- The address the counter's log lives at after the run. -/
  logAddressAfter : USize
  /-- What the program returned. -/
  value : β
  /-- The counter the program left behind. -/
  counter : Counter

/-- Read an object's address as an `IO` action, and so before whatever the
caller does next. A plain `let` binding of the address can be scheduled at the
point the address is *used* instead, and a `let` of `address s.log` then keeps
the projected log alive across the program's run — one extra reference to the
log, which makes the program's own `record` copy it. Taking the address
through `IO` puts the read where it is written and drops the projection at
once. -/
def addressIO {α : Type} (x : @& α) : IO USize :=
  return address x

/-- Run `prog` on `s` and observe the counter and its log. -/
def observeCounter {β : Type} {P : Pre Counter} {Q : Post Counter β}
    (prog : HSt Counter P β Q) (s : Counter) (hp : P [] s)
    (hq : ∀ b l' s', Q [] s b l' s' → l'.held = 1) : IO (CounterRun β) := do
  let exclusiveBefore := exclusive s
  let structAddressBefore ← addressIO s
  let logAddressBefore ← addressIO s.log
  let r := prog.exec s hp hq
  let structAddressAfter ← addressIO r.2
  let logAddressAfter ← addressIO r.2.log
  let run : CounterRun β :=
    { exclusiveBefore, structAddressBefore, structAddressAfter, logAddressBefore,
      logAddressAfter, value := r.1, counter := r.2 }
  return run

/-- A fresh array of `n` consecutive values from `seed`, with room for one
more value. The pushes are impure, so the compiler cannot merge this
expression with another one and the caller holds the single reference to the
result. The room matters to the cases below: `Array.push` reallocates when the
array is full, so an array built exactly to size would change its address on
the next push for a reason that has nothing to do with sharing. Holding the
capacity fixed is what makes the address of the next push an observation about
whether the array was shared. -/
def freshArray (seed n : Nat) : IO (Array Nat) := do
  let mut a : Array Nat := Array.mkEmpty (n + 1)
  for i in [0:n] do
    a := a.push (seed + i)
  return a

/-- A fresh counter: `hits` at zero, and a fresh log of `n` values from
`seed`. -/
def freshCounter (seed n : Nat) : IO Counter := do
  let log ← freshArray seed n
  return { hits := 0, log := log }

/-! ## Turning a run into failures

Each helper returns the lines describing what did not hold; an empty array is
a case that passed. -/

/-- `#[]` when the two values agree, and one line naming the case, what was
expected and what was observed otherwise. -/
def disagree {α : Type} [BEq α] [Repr α] (name label : String)
    (expected observed : α) : Array String :=
  if expected == observed then #[] else
    #[s!"{name}: {label}: expected {repr expected}, observed {repr observed}"]

/-- `#[]` when the object was exclusively owned, or not, as the case expects,
and one line naming the case, what was handed to the program, the expectation
and the observation otherwise. -/
def exclusiveFailure (name what : String) (expected observed : Bool) : Array String :=
  if observed == expected then #[] else
    #[s!"{name}: the {what} handed to the program: expected exclusively owned = {expected}, observed exclusively owned = {observed}"]

/-- `#[]` when the two addresses are the same, or not, as the case expects,
and one line naming the case, the label, the expectation and both addresses
otherwise. -/
def addressFailure (name label : String) (expectedSame : Bool) (before after : USize) : Array String :=
  if (before == after) == expectedSame then #[] else
    let expected :=
      if expectedSame then "the same address, an update in place"
      else "a different address, a copy"
    #[s!"{name}: {label}: expected {expected}, observed {before}, then {after}"]

/-- `#[]` when `text` contains `marker`, and one line naming the case, the marker
that was expected and the text that was observed otherwise. -/
def markerFailure (name label marker text : String) : Array String :=
  if text.contains marker then #[] else
    #[s!"{name}: {label}: expected the marker {repr marker}, observed:\n{text}"]

/-- `#[]` when `text` contains `marker`, and one line naming the case, the marker
that was expected to be absent and the text that was observed otherwise. Its
control is `markerFailure` at the same detector on the other stream of the pair it
is used in, which reports that the marker is there when it is. -/
def absentMarkerFailure (name label marker text : String) : Array String :=
  if text.contains marker then
    #[s!"{name}: {label}: expected {repr marker} to be absent, observed:\n{text}"]
  else #[]

/-- `#[]` when the child exited with the expected status, and one line naming the
case, the expected and observed statuses, and the child's standard error
otherwise. -/
def exitFailure (name : String) (expected : UInt32) (out : IO.Process.Output) : Array String :=
  if out.exitCode == expected then #[] else
    #[s!"{name}: the exit status: expected {expected}, observed {out.exitCode}; the child's standard error was:\n{out.stderr}"]

/-- The assertions a uniquely owned array must satisfy: it was exclusive
before the run, the program left it at the same address, and it returned and
left the values the program wrote. -/
def inPlaceFailures {β : Type} [BEq β] [Repr β] (name : String) (run : Run β)
    (expectedValue : β) (expectedArray : Array Nat) : Array String :=
  exclusiveFailure name "array" true run.exclusiveBefore
  ++ addressFailure name "the array address" true run.addressBefore run.addressAfter
  ++ disagree name "the value the program returned" expectedValue run.value
  ++ disagree name "the array the program left behind" expectedArray run.array

/-- The assertions an array with a live second reference must satisfy: it was
not exclusive, the write copied rather than updated in place, and the
reference that was not written through kept its values. -/
def copyFailures {β : Type} [BEq β] [Repr β] (name : String) (run : Run β)
    (secondReference : Array Nat) (expectedSecondReference : Array Nat)
    (expectedValue : β) (expectedArray : Array Nat) : Array String :=
  exclusiveFailure name "array" false run.exclusiveBefore
  ++ addressFailure name "the array address" false run.addressBefore run.addressAfter
  ++ disagree name "the array the second reference still reads" expectedSecondReference secondReference
  ++ disagree name "the value the program returned" expectedValue run.value
  ++ disagree name "the array the program left behind" expectedArray run.array

/-- The assertions the counter's unique case must satisfy: it was exclusive
before the run, the program left the counter and its log at the same
addresses, and it returned and left the values the program wrote. -/
def counterInPlaceFailures (name : String) (run : CounterRun (Option Nat)) : Array String :=
  exclusiveFailure name "counter" true run.exclusiveBefore
  ++ addressFailure name "the counter address" true run.structAddressBefore run.structAddressAfter
  ++ addressFailure name "the log address" true run.logAddressBefore run.logAddressAfter
  ++ disagree name "the value the program returned" (some 10) run.value
  ++ disagree name "the counter's hits" 1 run.counter.hits
  ++ disagree name "the counter's log" #[10, 11, 12, 13, 7] run.counter.log

/-! ## The cases

Each case builds its object, runs its program, and reports the failures. -/

/-- The P1 case on an array the caller alone refers to. -/
def uniqueCase (name : String) : IO (Array String) := do
  let fresh ← freshArray 10 4
  return inPlaceFailures name (observe p1 fresh (by hst_vc) (by hst_vc)) (some 7) #[7, 9, 12, 13]

/-- The readers case on an array the caller alone refers to. -/
def readersCase (name : String) : IO (Array String) := do
  let fresh ← freshArray 10 4
  return inPlaceFailures (β := Option Nat × Option Nat × Option Nat) name
    (observe p2 fresh (by hst_vc) (by hst_vc)) (some 11, some 12, some 13) #[1, 2, 12, 13]

/-- The P1 case on an array a second binding still refers to. `kept` is read
after the run, so the array it names stays alive throughout and the program's
reference cannot be the only one. -/
def sharedCase (name : String) : IO (Array String) := do
  let shared ← freshArray 10 4
  let kept := shared
  let run := observe p1 shared (by hst_vc) (by hst_vc)
  return copyFailures name run kept #[10, 11, 12, 13] (some 7) #[7, 9, 12, 13]

/-- The literal case: `#[10, 11, 12, 13]` is a closed term, so the compiler
emits it once as a persistent object — a constant with no reference count —
and every use of it names that one object, which can never be exclusively
owned. The value written comes from the caller, so this run is not folded
away at compile time. The array the program leaves behind is a fresh copy with
the written value, and the literal the program was handed is untouched. -/
def literalCase (name : String) (seed : Nat) : IO (Array String) := do
  let literal : Array Nat := #[10, 11, 12, 13]
  let prog := write (σ := Array Nat) (0, seed) >>>= fun _ => ret seed
  let run := observe prog literal (by hst_vc) (by hst_vc)
  let failures : Array String :=
    exclusiveFailure name "array" false run.exclusiveBefore
      ++ addressFailure name "the array address" false run.addressBefore run.addressAfter
      ++ disagree name "the value the program returned" seed run.value
      ++ disagree name "the array the program left behind" #[seed, 11, 12, 13] run.array
  return failures

/-- The counter case on a counter the caller alone refers to. -/
def counterUniqueCase (name : String) : IO (Array String) := do
  let s ← freshCounter 10 4
  return counterInPlaceFailures name (← observeCounter counterProg s (by hst_vc) (by hst_vc))

/-- The counter case with a live reference to the log outside the counter. The
structure is still exclusive, so `bump` and `record` update it in place; the
log is not, so `record`'s push copies it, its address changes, and the outside
reference keeps the values it had. -/
def counterSharedCase (name : String) : IO (Array String) := do
  let s ← freshCounter 10 4
  let keptLog := s.log
  let run ← observeCounter counterProg s (by hst_vc) (by hst_vc)
  let keptAfter := keptLog
  let failures : Array String :=
    exclusiveFailure name "counter" true run.exclusiveBefore
      ++ addressFailure name "the counter address" true run.structAddressBefore run.structAddressAfter
      ++ addressFailure name "the log address" false run.logAddressBefore run.logAddressAfter
      ++ disagree name "the value the program returned" (some 10) run.value
      ++ disagree name "the counter's hits" 1 run.counter.hits
      ++ disagree name "the counter's log" #[10, 11, 12, 13, 7] run.counter.log
      ++ disagree name "the log the outside reference still reads" #[10, 11, 12, 13] keptAfter
  return failures

/-- The counter's bump alone, with a live reference to the log outside the
counter: the write touches only `hits`, so the counter is updated in place,
the log is never written, and the outside reference is unaffected. -/
def counterSharedBumpCase (name : String) : IO (Array String) := do
  let s ← freshCounter 10 4
  let keptLog := s.log
  let run ← observeCounter counterBumpProg s (by hst_vc) (by hst_vc)
  let keptAfter := keptLog
  let failures : Array String :=
    exclusiveFailure name "counter" true run.exclusiveBefore
      ++ addressFailure name "the counter address" true run.structAddressBefore run.structAddressAfter
      ++ addressFailure name "the log address" true run.logAddressBefore run.logAddressAfter
      ++ disagree name "the counter's hits" 1 run.counter.hits
      ++ disagree name "the log the outside reference still reads" #[10, 11, 12, 13] keptAfter
  return failures

/-! ## The structured interface

`Scidonia.FracPerm.Structured` is the structured interface: a `Reader` with no
write, a `Program` whose one write is `Program.set`, and a notional
`Reader.parallel` whose shipped executor runs the branches one after the other.
The array is created inside `runFresh` and never leaves the executor, so these
cases observe the programs' results, and the checked children add the one thing
a value cannot show: that every `set` of these programs updated in place.

The detector is the same `assertExclusiveArray` the existing interface runs
before `update`: `set` calls it with the site
`Scidonia.FracPerm.Structured.set`, and `HSt.write` calls it with the site
`Scidonia.FracPerm.HSt.write`. Two existing cases are its controls, and they
control different things. `checked-abort` is the armed-check control: it shows
the check terminating a child process, with a write site on standard error, when
the write really would copy. `shared-copies` is the address control beside it:
it shows the copy itself, by the array's address changing under a live second
reference while the original keeps its values. A harness-only hook that shared a
structured session's array would be a third control, and it cannot exist under
the sealed design — Lean privacy is per module, so a hook that reached the
private interpreter would be importable by every client, and `runFresh` is the
only runner of the sealed executor. -/

open Scidonia.FracPerm.Structured

/-- The structured program of the `structured-unique` case: write, then a read
phase with nested parallel readers and a size observation, then two more
writes. The read phase sits between writes, so what it observes is what the
first write left. -/
def structuredProgram :
    Program (Option UInt64 × Option UInt64 × Nat × Bool × Bool × Bool) := do
  let w0 ← Program.set 0 17
  let r ← Program.readPhase
    (Reader.parallel (Reader.parallel (Reader.get 0) (Reader.get 1)) Reader.size)
  let w1 ← Program.set 1 23
  let w2 ← Program.set 2 29
  return (r.1.1, r.1.2, r.2, w0, w1, w2)

/-- The reader of the `structured-closure` case: it returns a closure over the
observations it made. The closure captures an `Option UInt64` and a `Nat`, not
the array, which is the point of the case. -/
def structuredClosureReader : Reader (Nat → Nat) := do
  let a ← Reader.get 0
  let n ← Reader.size
  return fun k => match a with
    | some v => v.toNat + k
    | none => n + k

/-- The structured program of the `structured-closure` case: write, a read
phase whose result is a closure, then a second write, which must still be in
place once the closure has crossed the join. -/
def structuredClosureProgram : Program (Nat × Bool) := do
  let w0 ← Program.set 0 17
  let r ← Program.readPhase structuredClosureReader
  let w1 ← Program.set 1 5
  return (r 3, w0 && w1)

/-- What the structured cases start from. The fill comes from the caller, so the
compiler cannot turn `Array.replicate` into a persistent constant on the path
the harness measures. -/
def structuredInit (fill : UInt64) : Init := { size := 8, fill }

/-- The `structured-unique` case: the value is what the program's writes and
observations require. -/
def structuredUniqueCase (name : String) (fill : UInt64) : IO (Array String) := do
  let r ← runFresh (structuredInit fill) structuredProgram
  return disagree name "the value the program returned"
    (some 17, some fill, 8, true, true, true) r

/-- The `structured-closure` case: the closure returned by the read phase is
applied after the phase, and the second write still returns `true`. -/
def structuredClosureCase (name : String) (fill : UInt64) : IO (Array String) := do
  let r ← runFresh (structuredInit fill) structuredClosureProgram
  return disagree name "the value the program returned" (20, true) r

/-! ## Child processes

The check turns a copied write into a terminated process, so the case that
shows it firing has to be a child: the parent launches itself again with
`SCIDONIA_CHECK_INPLACE=1` and reads the exit status and the streams. -/

/-- This executable, run again with the in-place check enabled and the given
subcommand. -/
def launchChecked (command : String) : IO IO.Process.Output := do
  let exe ← IO.appPath
  IO.Process.output {
    cmd := exe.toString
    args := #[command]
    env := #[("SCIDONIA_CHECK_INPLACE", some "1")]
  }

/-- The shared case in a child with the check enabled must end the process,
with the write site on standard error, and must have reported the check
enabled before it did. -/
def checkedAbortCase : IO (Array String) := do
  let out ← launchChecked "shared"
  let status :=
    if out.exitCode == 0 then
      #[s!"checked-abort: the exit status: expected a nonzero status, observed {out.exitCode}"]
    else #[]
  let failures :=
    markerFailure "checked-abort" "the child's standard output" "check-enabled=true" out.stdout
      ++ status
      ++ markerFailure "checked-abort" "the child's standard error" "Scidonia.FracPerm.HSt.write" out.stderr
  return failures

/-- The unique case in a child with the check enabled must pass: the check is
armed and does not fire on an update in place. -/
def checkedUniqueCase : IO (Array String) := do
  let out ← launchChecked "unique"
  let failures :=
    markerFailure "checked-unique" "the child's standard output" "check-enabled=true" out.stdout
      ++ exitFailure "checked-unique" 0 out
      ++ markerFailure "checked-unique" "the child's standard output" "ok   unique" out.stdout
  return failures

/-- The counter's unique case in a child with the check enabled must pass: the
check is armed and the counter's structure and log are both exclusively owned,
so nothing copies. -/
def counterCheckedUniqueCase : IO (Array String) := do
  let out ← launchChecked "counter-unique"
  let failures :=
    markerFailure "counter-checked-unique" "the child's standard output" "check-enabled=true" out.stdout
      ++ exitFailure "counter-checked-unique" 0 out
      ++ markerFailure "counter-checked-unique" "the child's standard output" "ok   counter-unique" out.stdout
  return failures

/-- The counter's shared-log case in a child with the check enabled must end
the process, naming the log field: the counter itself is exclusive, so only
the counter's own check of its log can catch the copy `record` would take. -/
def counterCheckedAbortCase : IO (Array String) := do
  let out ← launchChecked "counter-shared"
  let status :=
    if out.exitCode == 0 then
      #[s!"counter-checked-abort: the exit status: expected a nonzero status, observed {out.exitCode}"]
    else #[]
  let failures :=
    markerFailure "counter-checked-abort" "the child's standard output" "check-enabled=true" out.stdout
      ++ status
      ++ markerFailure "counter-checked-abort" "the child's standard error"
        "the Counter's log field is not exclusively owned" out.stderr
  return failures

/-- The counter's bump case in a child with the check enabled must pass even
though the log is shared: `bump` writes only `hits`, so nothing this write
touches would copy. This is the control for the case above: the same shared
log must not be fatal for a write that does not touch it. -/
def counterCheckedBumpCase : IO (Array String) := do
  let out ← launchChecked "counter-shared-bump"
  let failures :=
    markerFailure "counter-checked-bump" "the child's standard output" "check-enabled=true" out.stdout
      ++ exitFailure "counter-checked-bump" 0 out
      ++ markerFailure "counter-checked-bump" "the child's standard output" "ok   counter-shared-bump" out.stdout
  return failures

/-- The `structured-unique` case in a child with the check enabled: the check
is armed and does not fire on any of the three writes, so the child exits zero
having reported the check enabled and the case ok. -/
def checkedStructuredUniqueCase : IO (Array String) := do
  let out ← launchChecked "structured-unique"
  let failures :=
    markerFailure "structured-checked-unique" "the child's standard output" "check-enabled=true" out.stdout
      ++ exitFailure "structured-checked-unique" 0 out
      ++ markerFailure "structured-checked-unique" "the child's standard output" "ok   structured-unique" out.stdout
  return failures

/-- The `structured-closure` case in a child with the check enabled: the closure
the read phase returned is live across the second write, which must still be in
place. -/
def checkedStructuredClosureCase : IO (Array String) := do
  let out ← launchChecked "structured-closure"
  let failures :=
    markerFailure "structured-checked-closure" "the child's standard output" "check-enabled=true" out.stdout
      ++ exitFailure "structured-checked-closure" 0 out
      ++ markerFailure "structured-checked-closure" "the child's standard output" "ok   structured-closure" out.stdout
  return failures

/-! ## The path write on an array of structs

`Scidonia.FracPerm.StateVar.Layout5` writes a leaf by taking its whole path
apart: `takeOut` exchanges the selected element with the layout's placeholder in
an owned `Array.swapAt`, and the inverse exchange puts the focus back after the
path below it has been written. The cases here observe that take-out on an
`Array (UInt64 × UInt64)`: the array's buffer must keep its address, the sibling
structs must be the same objects, and the value at the path must be the one
written while a sibling's stays fixed. A live second reference to the array must
make the write copy instead.

The struct at the written index is a `Prod`. The fused update returns the state
alone, so the compiler's reset/reuse pass rewrites that cell in place — the
generated C tests `lean_is_exclusive` and then sets the cell's fields — and
`layout5-unique` asserts that the cell keeps its address. When a live second
reference reaches it the test fails and the cell is allocated afresh, which is
what `layout5-shared-copies` asserts: its address changes there. The array's
buffer and every struct the write does not touch keep their addresses either,
and those are asserted in every unique case.

Where the focused element is itself an array — the nested cases — that array's
own address is the same measurement: `layout5-nest` asserts it is unchanged,
because the take-out hands the inner array over exclusively and the check on it
is armed and does not fire, while `layout5-nest-aliased` holds a second
reference to that inner array and asserts its address *changes* (the outer
array's does not). That copy is what the element check turns into an abort in
the checked child `layout5-checked-nest-shared`, and `layout5-checked-nest` is
the unique nested write with both checks armed and neither firing. -/

/-- The layout of the path-write cases: an array of binary structs, each a pair
of machine words. -/
abbrev layout5Structs : Layout5.Layout := .arr (.struct (.leaf .uint) (.leaf .uint))

/-- The path `.index 3 (.left .here)`: the first field of the struct at index 3,
which is neither the array's first nor its last slot. -/
def layout5LeftPath : Layout5.ObsPath layout5Structs :=
  ⟨.index 3 (.left .here), .uint, rfl⟩

/-- The path `.index 5 (.right .here)`: the second field of a different struct. -/
def layout5RightPath : Layout5.ObsPath layout5Structs :=
  ⟨.index 5 (.right .here), .uint, rfl⟩

/-- The path `.index 7 (.left .here)`: the last slot, where the swap is with
itself. -/
def layout5LastPath : Layout5.ObsPath layout5Structs :=
  ⟨.index 7 (.left .here), .uint, rfl⟩

/-- The path `.index 9 (.left .here)`: past the array, so the write declines and
leaves the state alone. -/
def layout5BadPath : Layout5.ObsPath layout5Structs :=
  ⟨.index 9 (.left .here), .uint, rfl⟩

/-- A fresh array of `n` structs from `seed`, with room for one more element, so
that the take-out and put-back cycle does not have to grow the buffer. -/
def freshStructs (seed n : Nat) : IO (Array (UInt64 × UInt64)) := do
  let mut a : Array (UInt64 × UInt64) := Array.mkEmpty (n + 1)
  for i in [0:n] do
    a := a.push ((seed + i).toUInt64, (seed + 100 + i).toUInt64)
  return a

/-- What one run of a path write leaves to check. -/
structure PathRun where
  /-- Whether the array handed to the write was exclusively owned. -/
  exclusiveBefore : Bool
  /-- The array's buffer address before the write. -/
  arrayBefore : USize
  /-- The array's buffer address after the write. -/
  arrayAfter : USize
  /-- The address of the sibling struct at index 0, before the write. -/
  siblingBefore : USize
  /-- The address of the sibling struct at index 0, after the write. -/
  siblingAfter : USize
  /-- The address of the struct at the written index, before the write. -/
  focusedBefore : USize
  /-- The address of the struct at the written index, after the write. -/
  focusedAfter : USize
  /-- Whether the write reported that it took effect. -/
  ok : Bool
  /-- The array the write left behind. -/
  array : Array (UInt64 × UInt64)

/-- Run `write` on `a` and observe the array's and the structs' addresses. `a`
is consumed by the run, so a caller that passes its only reference sees
`exclusiveBefore` as `true`. -/
def observePath (write : Array (UInt64 × UInt64) → Array (UInt64 × UInt64) × Bool)
    (a : Array (UInt64 × UInt64)) : IO PathRun := do
  let exclusiveBefore := exclusive a
  let arrayBefore ← addressIO a
  let siblingBefore ← addressIO (a[0]!)
  let focusedBefore ← addressIO (a[3]!)
  let (s', ok) := write a
  let arrayAfter ← addressIO s'
  let siblingAfter ← addressIO (s'[0]!)
  let focusedAfter ← addressIO (s'[3]!)
  return { exclusiveBefore, arrayBefore, arrayAfter, siblingBefore, siblingAfter,
           focusedBefore, focusedAfter, ok, array := s' }

/-- The unique case: the array's buffer, the structs the write does not touch
and the struct at the written index all keep their addresses, the write reports
that it took effect, and the value at the path changes while a sibling's stays
fixed. The focused struct's address is asserted: the fused update reuses the
pair when it is exclusively owned. -/
def layout5UniqueCase (name : String) (seed : Nat) : IO (Array String) := do
  let a ← freshStructs seed 8
  let run ← observePath (fun arr => Layout5.setLeaf layout5LeftPath (seed + 7).toUInt64 arr) a
  IO.println s!"{name}: the struct at the written index: {run.focusedBefore}, then {run.focusedAfter}"
  let failures : Array String :=
    exclusiveFailure name "array" true run.exclusiveBefore
      ++ addressFailure name "the array address" true run.arrayBefore run.arrayAfter
      ++ addressFailure name "the sibling struct's address" true run.siblingBefore run.siblingAfter
      ++ addressFailure name "the struct at the written index" true run.focusedBefore run.focusedAfter
      ++ disagree name "the write took effect" true run.ok
      ++ disagree name "the value at the path" ((seed + 7).toUInt64, (seed + 103).toUInt64) (run.array[3]!)
      ++ disagree name "a sibling element" ((seed).toUInt64, (seed + 100).toUInt64) (run.array[0]!)
      ++ disagree name "the array size" 8 run.array.size
  return failures

/-- The second field of another struct, so that the case is not specific to the
left field or to one index. The struct at index 3, which this write does not
touch, keeps its address. -/
def layout5RightCase (name : String) (seed : Nat) : IO (Array String) := do
  let a ← freshStructs seed 8
  let run ← observePath (fun arr => Layout5.setLeaf layout5RightPath (seed + 9).toUInt64 arr) a
  let failures : Array String :=
    exclusiveFailure name "array" true run.exclusiveBefore
      ++ addressFailure name "the array address" true run.arrayBefore run.arrayAfter
      ++ addressFailure name "a struct the write does not touch" true run.focusedBefore run.focusedAfter
      ++ disagree name "the write took effect" true run.ok
      ++ disagree name "the value at the path" ((seed + 5).toUInt64, (seed + 9).toUInt64) (run.array[5]!)
      ++ disagree name "the array size" 8 run.array.size
  return failures

/-- The last-slot case: the take-out swaps the selected slot with itself, so the
siblings array is the array's prefix and the round trip still lands the focus at
the last index. The struct at index 3, which this write does not touch, keeps
its address. -/
def layout5LastCase (name : String) (seed : Nat) : IO (Array String) := do
  let a ← freshStructs seed 8
  let run ← observePath (fun arr => Layout5.setLeaf layout5LastPath (seed + 8).toUInt64 arr) a
  let failures : Array String :=
    exclusiveFailure name "array" true run.exclusiveBefore
      ++ addressFailure name "the array address" true run.arrayBefore run.arrayAfter
      ++ addressFailure name "a struct the write does not touch" true run.focusedBefore run.focusedAfter
      ++ disagree name "the write took effect" true run.ok
      ++ disagree name "the value at the path" ((seed + 8).toUInt64, (seed + 107).toUInt64) (run.array[7]!)
      ++ disagree name "the array size" 8 run.array.size
  return failures

/-- The out-of-bounds case: the write reports that it did not take effect and
the state is the one it was handed, address included. -/
def layout5BadCase (name : String) (seed : Nat) : IO (Array String) := do
  let a ← freshStructs seed 8
  let run ← observePath (fun arr => Layout5.setLeaf layout5BadPath (seed + 1).toUInt64 arr) a
  let failures : Array String :=
    exclusiveFailure name "array" true run.exclusiveBefore
      ++ addressFailure name "the array address" true run.arrayBefore run.arrayAfter
      ++ disagree name "the write took effect" false run.ok
      ++ disagree name "the element the write did not touch" ((seed + 3).toUInt64, (seed + 103).toUInt64) (run.array[3]!)
      ++ disagree name "the array size" 8 run.array.size
  return failures

/-- The aliased case: a second binding still refers to the array, so it is not
exclusively owned, the write copies rather than updating in place, the struct at
the written index is rebuilt at a new address, and the reference the write did
not go through keeps its values. -/
def layout5AliasedCase (name : String) (seed : Nat) : IO (Array String) := do
  let a ← freshStructs seed 8
  let kept := a
  let run ← observePath (fun arr => Layout5.setLeaf layout5LeftPath (seed + 7).toUInt64 arr) a
  let keptAfter := kept
  let failures : Array String :=
    exclusiveFailure name "array" false run.exclusiveBefore
      ++ addressFailure name "the array address" false run.arrayBefore run.arrayAfter
      ++ addressFailure name "the struct at the written index" false run.focusedBefore run.focusedAfter
      ++ disagree name "the write took effect" true run.ok
      ++ disagree name "the value at the path" ((seed + 7).toUInt64, (seed + 103).toUInt64) (run.array[3]!)
      ++ disagree name "the value the alias still reads" ((seed + 3).toUInt64, (seed + 103).toUInt64) (keptAfter[3]!)
  return failures

/-- The path-write cases in a child with the check enabled: the array is
exclusively owned and the extracted struct is too, so the check is armed and
does not fire. -/
def checkedLayout5UniqueCase : IO (Array String) := do
  let out ← launchChecked "layout5-unique"
  let failures :=
    markerFailure "layout5-checked-unique" "the child's standard output" "check-enabled=true" out.stdout
      ++ exitFailure "layout5-checked-unique" 0 out
      ++ markerFailure "layout5-checked-unique" "the child's standard output" "ok   layout5-unique" out.stdout
  return failures

/-- The aliased path write in a child with the check enabled must end the
process, naming the `Layout5` site: the write is about to copy the array. -/
def checkedLayout5AliasedCase : IO (Array String) := do
  let out ← launchChecked "layout5-shared"
  let status :=
    if out.exitCode == 0 then
      #[s!"layout5-checked-shared: the exit status: expected a nonzero status, observed {out.exitCode}"]
    else #[]
  let failures :=
    markerFailure "layout5-checked-shared" "the child's standard output" "check-enabled=true" out.stdout
      ++ status
      ++ markerFailure "layout5-checked-shared" "the child's standard error"
        "Scidonia.FracPerm.StateVar.Layout5.open" out.stderr
  return failures


/-- The layout of the nested-array case: an array of arrays of machine words. The
focused element is itself a mutable array, so a write inside it is an update of
*that* array and its address is what a unique write must keep and an aliased
write must change. -/
abbrev layout5Nest : Layout5.Layout := .arr (.arr (.leaf .uint))

/-- The path `.index 2 (.index 1 .here)`: the second slot of the inner array at
index 2. -/
def layout5NestPath : Layout5.ObsPath layout5Nest := ⟨.index 2 (.index 1 .here), .uint, rfl⟩

/-- A fresh array of `n` inner arrays of machine words, with room for one more
element so a take-out does not have to grow the buffer. -/
def freshNested (seed n : Nat) : IO (Array (Array UInt64)) := do
  let mut a : Array (Array UInt64) := Array.mkEmpty (n + 1)
  for i in [0:n] do
    let mut inner : Array UInt64 := Array.mkEmpty 4
    for j in [0:3] do
      inner := inner.push ((seed + 10 * i + j).toUInt64)
    a := a.push inner
  return a

/-- What one run of the nested-array write leaves to check: the outer array's
address, the inner array's address before and after, and the values. -/
structure NestRun where
  /-- Whether the outer array was exclusively owned. -/
  outerExclusive : Bool
  /-- Whether the focused inner array was exclusively owned. -/
  innerExclusive : Bool
  /-- The outer array's address before and after. -/
  outerBefore : USize
  outerAfter : USize
  /-- The focused inner array's address before and after. -/
  innerBefore : USize
  innerAfter : USize
  /-- Whether the write took effect. -/
  ok : Bool
  /-- The outer array the write left behind. -/
  outer : Array (Array UInt64)
  /-- The inner array the write left at the focused index. -/
  inner : Array UInt64

/-- Run the nested write and observe both arrays' addresses. -/
def observeNest (outer : Array (Array UInt64)) : IO NestRun := do
  let outerExclusive := exclusive outer
  let innerExclusive := exclusive (outer[2]!)
  let outerBefore ← addressIO outer
  let innerBefore ← addressIO (outer[2]!)
  let r := Layout5.setLeaf layout5NestPath (99 : UInt64) outer
  let outerAfter ← addressIO r.1
  let innerAfter ← addressIO (r.1[2]!)
  return { outerExclusive, innerExclusive, outerBefore, outerAfter, innerBefore, innerAfter,
           ok := r.2, outer := r.1, inner := r.1[2]! }

/-- The nested unique case: the outer array and the focused inner array are both
exclusively owned, both keep their addresses, the write landed, and every other
slot of the inner array is unchanged. -/
def layout5NestCase (name : String) (seed : Nat) : IO (Array String) := do
  let a ← freshNested seed 4
  let run ← observeNest a
  let failures : Array String :=
    exclusiveFailure name "outer array" true run.outerExclusive
      ++ exclusiveFailure name "focused inner array" true run.innerExclusive
      ++ addressFailure name "the outer array address" true run.outerBefore run.outerAfter
      ++ addressFailure name "the focused inner array address" true run.innerBefore run.innerAfter
      ++ disagree name "the write took effect" true run.ok
      ++ disagree name "the value at the path" (99 : UInt64) run.inner[1]!
      ++ disagree name "a sibling slot of the inner array" (seed + 20).toUInt64 run.inner[0]!
      ++ disagree name "another inner array" (seed).toUInt64 (run.outer[0]!)[0]!
  return failures

/-- The element-alias control: a live second reference to the *focused inner
array* (not to the outer one) makes that array shared, so writing its slot copies
it: its address changes and the alias keeps its values, while the outer array
still keeps its own address. -/
def layout5NestAliasedCase (name : String) (seed : Nat) : IO (Array String) := do
  let a ← freshNested seed 4
  let kept := a[2]!
  let run ← observeNest a
  let keptAfter := kept
  let failures : Array String :=
    addressFailure name "the outer array address" true run.outerBefore run.outerAfter
    ++ addressFailure name "the focused inner array address" false run.innerBefore run.innerAfter
    ++ disagree name "the write took effect" true run.ok
    ++ disagree name "the value at the path" (99 : UInt64) run.inner[1]!
    ++ disagree name "the value the alias still reads" (seed + 21).toUInt64 keptAfter[1]!
  return failures

/-- The nested unique write in a child with the check enabled: the outer array and
the focused inner array are both exclusively owned, so both checks are armed and
neither fires. -/
def checkedLayout5NestCase : IO (Array String) := do
  let out ← launchChecked "layout5-nest"
  let failures :=
    markerFailure "layout5-checked-nest" "the child's standard output" "check-enabled=true" out.stdout
      ++ exitFailure "layout5-checked-nest" 0 out
      ++ markerFailure "layout5-checked-nest" "the child's standard output" "ok   layout5-nest" out.stdout
  return failures

/-- The element-alias write in a child with the check enabled must end the
process naming the *focus* site: the outer array is exclusive, so it is the check
on the extracted element — the aliased inner array — that catches the copy. -/
def checkedLayout5NestAliasedCase : IO (Array String) := do
  let out ← launchChecked "layout5-nest-shared"
  let status :=
    if out.exitCode == 0 then
      #[s!"layout5-checked-nest-shared: the exit status: expected a nonzero status, observed {out.exitCode}"]
    else #[]
  let failures :=
    markerFailure "layout5-checked-nest-shared" "the child's standard output" "check-enabled=true" out.stdout
      ++ status
      ++ markerFailure "layout5-checked-nest-shared" "the child's standard error"
        "Scidonia.FracPerm.StateVar.Layout5.struct" out.stderr
  return failures

/-! ## The sealed write on an array of structs

`Scidonia.FracPerm.StateVar.SealedStateVar` is the interface an author joins when
the type *is* a layout's state type: it supplies the layout and the equality and
no code, so the write is the layout's `setLeaf` through the cast in `rep`. The
case here drives that write on the shipped `Array (UInt64 × UInt64)` instance
(whose `rep` is `rfl`, so the cast erases) and measures exactly what
`layout5-unique` measures: the array's buffer and the struct cell at the written
index must both keep their addresses, and the value at the path must be the one
written. The checked child is the same write with both `assertExclusive` checks
armed and neither firing. -/

/-- The path `.index 3 (.left .here)` at the sealed array-of-structs layout. -/
def sealedPairPath : Layout5.ObsPath SealedStateVar.sealedPairs :=
  ⟨.index 3 (.left .here), .uint, rfl⟩

/-- The sealed unique case: the write is `SealedStateVar.setLeaf` at the shipped
`Array (UInt64 × UInt64)` instance, and the root array's buffer address and the
struct cell at the written index must both be unchanged. -/
def sealedUniqueCase (name : String) (seed : Nat) : IO (Array String) := do
  let a ← freshStructs seed 8
  let run ← observePath
    (fun (arr : Array (UInt64 × UInt64)) =>
      SealedStateVar.setLeaf sealedPairPath (seed + 7).toUInt64 arr) a
  IO.println s!"{name}: the struct at the written index: {run.focusedBefore}, then {run.focusedAfter}"
  let failures : Array String :=
    exclusiveFailure name "array" true run.exclusiveBefore
      ++ addressFailure name "the array address" true run.arrayBefore run.arrayAfter
      ++ addressFailure name "the sibling struct's address" true run.siblingBefore run.siblingAfter
      ++ addressFailure name "the struct at the written index" true run.focusedBefore run.focusedAfter
      ++ disagree name "the write took effect" true run.ok
      ++ disagree name "the value at the path" ((seed + 7).toUInt64, (seed + 103).toUInt64) (run.array[3]!)
      ++ disagree name "a sibling element" ((seed).toUInt64, (seed + 100).toUInt64) (run.array[0]!)
      ++ disagree name "the array size" 8 run.array.size
  return failures

/-- The sealed write in a child with the check enabled: the array and the
extracted struct are exclusively owned, so both checks are armed and neither
fires, and the child exits zero. -/
def checkedSealedUniqueCase : IO (Array String) := do
  let out ← launchChecked "sealed-unique"
  let failures :=
    markerFailure "sealed-checked-unique" "the child's standard output" "check-enabled=true" out.stdout
      ++ exitFailure "sealed-checked-unique" 0 out
      ++ markerFailure "sealed-checked-unique" "the child's standard output" "ok   sealed-unique" out.stdout
  return failures

/-! ## The update examples

`ScidoniaExamples.Updates` is the example library of updates: a flat array
(`arrSet`, the Lean primitive), a nested array (`nestedSet`, a two-step path write
through the sealed class) and a struct tree of depth `k` (`treeSet`, a path write
of depth `k` through the sealed class). Each case below observes the addresses the
update is about — the flat array's buffer, the nested array's outer buffer and
focused inner array, and the tree's spine cells down the written path — with the
same `addressIO` instrument the path-write cases use. The unique case asserts the
addresses are kept, which is the update in place; the aliased case holds a live
second reference and asserts they change, which is the copy.

The tree cases run at depth four: four cells on the spine, which the case prints,
and a leaf at the end of four left steps. A live reference to the tree makes every
cell on the path shared, each level's projection then copies, and all four cells
are rebuilt — that is the O(log n) allocation the write costs when the tree is not
exclusively owned. -/

/-- A fresh array of `n` machine words from `seed`, with room for one more, built
by run-time pushes so that the caller holds the single reference. -/
def freshWords (seed n : Nat) : IO (Array UInt64) := do
  let mut a : Array UInt64 := Array.mkEmpty (n + 1)
  for i in [0:n] do
    a := a.push (seed + i).toUInt64
  return a

/-- What one run of the flat-array update leaves to check. -/
structure ArrayRun where
  /-- Whether the array handed to the update was exclusively owned. -/
  exclusiveBefore : Bool
  /-- The array's buffer address before the update. -/
  addressBefore : USize
  /-- The array's buffer address after the update. -/
  addressAfter : USize
  /-- The array the update left behind. -/
  array : Array UInt64

/-- Run `arrSet` on `a` and observe the buffer's address. -/
def observeArrSet (a : Array UInt64) (i : Nat) (v : UInt64) : IO ArrayRun := do
  let exclusiveBefore := exclusive a
  let addressBefore ← addressIO a
  let a' := arrSet a i v
  let addressAfter ← addressIO a'
  return { exclusiveBefore, addressBefore, addressAfter, array := a' }

/-- The flat-array update on an array the caller alone refers to: the buffer keeps
its address — one slot was written in place — the written slot holds the new word,
a sibling slot holds its own, and the array keeps its size. -/
def updatesArrayUniqueCase (name : String) (seed : Nat) : IO (Array String) := do
  let a ← freshWords seed 8
  let run ← observeArrSet a 3 (seed + 7).toUInt64
  IO.println s!"{name}: the buffer address: {run.addressBefore}, then {run.addressAfter}"
  let failures : Array String :=
    exclusiveFailure name "array" true run.exclusiveBefore
      ++ addressFailure name "the buffer address" true run.addressBefore run.addressAfter
      ++ disagree name "the value at the written index" (seed + 7).toUInt64 run.array[3]!
      ++ disagree name "a sibling slot" seed.toUInt64 run.array[0]!
      ++ disagree name "the array size" 8 run.array.size
  return failures

/-- The flat-array update with a live second reference to the array: it is not
exclusively owned, the write replaces the buffer with a copy, the address changes,
and the reference the write did not go through keeps its values. -/
def updatesArraySharedCase (name : String) (seed : Nat) : IO (Array String) := do
  let a ← freshWords seed 8
  let kept := a
  let run ← observeArrSet a 3 (seed + 7).toUInt64
  let keptAfter := kept
  IO.println s!"{name}: the buffer address: {run.addressBefore}, then {run.addressAfter}"
  let failures : Array String :=
    exclusiveFailure name "array" false run.exclusiveBefore
      ++ addressFailure name "the buffer address" false run.addressBefore run.addressAfter
      ++ disagree name "the value at the written index" (seed + 7).toUInt64 run.array[3]!
      ++ disagree name "the value the alias still reads" (seed + 3).toUInt64 keptAfter[3]!
      ++ disagree name "the array size" 8 run.array.size
  return failures

/-- Run the nested-array update of the examples library on the inner array at index
2 and observe the outer array's and that inner array's addresses. -/
def observeUpdatesNest (outer : Array (Array UInt64)) (v : UInt64) : IO NestRun := do
  let outerExclusive := exclusive outer
  let innerExclusive := exclusive (outer[2]!)
  let outerBefore ← addressIO outer
  let innerBefore ← addressIO (outer[2]!)
  let r := nestedSet outer 2 1 v
  let outerAfter ← addressIO r.1
  let innerAfter ← addressIO (r.1[2]!)
  return { outerExclusive, innerExclusive, outerBefore, outerAfter, innerBefore, innerAfter,
           ok := r.2, outer := r.1, inner := r.1[2]! }

/-- The nested-array update on an outer array and a focused inner array the caller
alone refers to: both keep their addresses — each level was updated in place — the
written slot holds the new word, a sibling slot of the inner array and another
inner array hold theirs, and the write reported that it took effect. -/
def updatesNestedUniqueCase (name : String) (seed : Nat) : IO (Array String) := do
  let a ← freshNested seed 4
  let run ← observeUpdatesNest a 99
  IO.println s!"{name}: the outer array address: {run.outerBefore}, then {run.outerAfter}; the focused inner array address: {run.innerBefore}, then {run.innerAfter}"
  let failures : Array String :=
    exclusiveFailure name "outer array" true run.outerExclusive
      ++ exclusiveFailure name "focused inner array" true run.innerExclusive
      ++ addressFailure name "the outer array address" true run.outerBefore run.outerAfter
      ++ addressFailure name "the focused inner array address" true run.innerBefore run.innerAfter
      ++ disagree name "the write took effect" true run.ok
      ++ disagree name "the value at the path" (99 : UInt64) run.inner[1]!
      ++ disagree name "a sibling slot of the inner array" (seed + 20).toUInt64 run.inner[0]!
      ++ disagree name "another inner array" (seed).toUInt64 (run.outer[0]!)[0]!
  return failures

/-- The nested-array update with a live second reference to the *focused inner
array*: that level copies, so the inner array's address changes and the alias
keeps its values, while the outer array still keeps its own address. -/
def updatesNestedSharedCase (name : String) (seed : Nat) : IO (Array String) := do
  let a ← freshNested seed 4
  let kept := a[2]!
  let run ← observeUpdatesNest a 99
  let keptAfter := kept
  IO.println s!"{name}: the outer array address: {run.outerBefore}, then {run.outerAfter}; the focused inner array address: {run.innerBefore}, then {run.innerAfter}"
  let failures : Array String :=
    addressFailure name "the outer array address" true run.outerBefore run.outerAfter
      ++ addressFailure name "the focused inner array address" false run.innerBefore run.innerAfter
      ++ disagree name "the write took effect" true run.ok
      ++ disagree name "the value at the path" (99 : UInt64) run.inner[1]!
      ++ disagree name "the value the alias still reads" (seed + 21).toUInt64 keptAfter[1]!
  return failures

/-- The addresses of a struct tree's spine cells, from the root down the all-left
path: the cells the update's recursion walks and rebuilds. A depth-`k` tree's
spine holds `k` such cells — the struct at depth `k`, the struct at depth `k - 1`
inside it, and so on down to the struct at depth `1` — and the walk stops before
the leaf, whose word is a scalar and has no cell of its own to observe.

Each address is read through `addressIO`, which is what keeps a read of a
projection from leaving a reference to it behind: a plain `let` of an address can
be scheduled at the point the address is used, and the projection then stays alive
across the update it was meant to observe. -/
def treeSpine : (k : Nat) → Layout5.State (structTree k) → IO (Array USize)
  | 0, _ => return #[]
  | k + 1, t => do
    let cell ← addressIO t
    let rest ← treeSpine k t.1
    return #[cell] ++ rest

/-- `#[]` when every spine cell kept its address, and one line naming the case, the
label and both lists otherwise. -/
def addressesKeptFailure (name label : String) (before after : Array USize) : Array String :=
  if before == after then #[] else
    #[s!"{name}: {label}: expected the same address at every cell, observed {repr before}, then {repr after}"]

/-- `#[]` when every spine cell's address changed and the two lists have the same
length, and one line naming the case, the label and both lists otherwise. -/
def addressesChangedFailure (name label : String) (before after : Array USize) : Array String :=
  if before.size == after.size && (before.zip after).all (fun p => p.1 != p.2) then #[] else
    #[s!"{name}: {label}: expected a different address at every cell, observed {repr before}, then {repr after}"]

/-- `#[]` when the read at a path observed the expected value, and one line naming
the case, the label, the expectation and the observation otherwise. The read
returns the library's `Option Value`, whose equality is decidable but which
`disagree` cannot use, so the comparison is `decide`d here. -/
def observationFailure (name label : String) (expected observed : Option Value) : Array String :=
  if decide (observed = expected) then #[] else
    #[s!"{name}: {label}: expected {repr expected}, observed {repr observed}"]

/-- What one run of the struct-tree update leaves to check. -/
structure TreeRun (k : Nat) where
  /-- Whether the tree handed to the update was exclusively owned. -/
  exclusiveBefore : Bool
  /-- The spine cells' addresses before the update, from the root down. -/
  spineBefore : Array USize
  /-- The spine cells' addresses after the update. -/
  spineAfter : Array USize
  /-- Whether the update reported that it took effect. -/
  ok : Bool
  /-- The tree the update left behind. -/
  tree : Layout5.State (structTree k)

/-- Run `treeSet` at the leftmost leaf of `t` and observe the spine cells'
addresses before and after. -/
def observeTreeSet (k : Nat) (v : UInt64) (t : Layout5.State (structTree k)) : IO (TreeRun k) := do
  let exclusiveBefore := exclusive t
  let spineBefore ← treeSpine k t
  let r := treeSet k v t
  let spineAfter ← treeSpine k r.1
  return { exclusiveBefore, spineBefore, spineAfter, ok := r.2, tree := r.1 }

/-- The struct-tree update on a tree the caller alone refers to: every spine cell
keeps its address — the recursion rewrote the cells it walked in place, so the
spine was built once and reused — the leftmost leaf holds the new word, and the
leaf beside it holds its own. -/
def updatesTreeUniqueCase (name : String) (seed : Nat) : IO (Array String) := do
  let t := treeFilled 4 seed.toUInt64
  let run ← observeTreeSet 4 (seed + 7).toUInt64 t
  IO.println s!"{name}: the spine cells: {repr run.spineBefore}, then {repr run.spineAfter}"
  let failures : Array String :=
    exclusiveFailure name "tree" true run.exclusiveBefore
      ++ addressesKeptFailure name "the spine cells" run.spineBefore run.spineAfter
      ++ disagree name "the write took effect" true run.ok
      ++ observationFailure name "the value at the path" (some (.uint (seed + 7).toUInt64))
        (SealedStateVar.read? (treePath 4) run.tree)
      ++ observationFailure name "the leaf beside it" (some (.uint (seed + 1).toUInt64))
        (SealedStateVar.read? (treeSiblingPath 3) run.tree)
  return failures

/-- The struct-tree update with a live second reference to the tree: the root is
shared, every cell on the written path is rebuilt, and the spine's addresses all
change, which is the O(log n) allocation the update costs when the tree is not
exclusively owned. The alias keeps the values it had. -/
def updatesTreeSharedCase (name : String) (seed : Nat) : IO (Array String) := do
  let t := treeFilled 4 seed.toUInt64
  let kept := t
  let run ← observeTreeSet 4 (seed + 7).toUInt64 t
  let keptAfter := kept
  IO.println s!"{name}: the spine cells: {repr run.spineBefore}, then {repr run.spineAfter}"
  let failures : Array String :=
    exclusiveFailure name "tree" false run.exclusiveBefore
      ++ addressesChangedFailure name "the spine cells" run.spineBefore run.spineAfter
      ++ disagree name "the write took effect" true run.ok
      ++ observationFailure name "the value at the path" (some (.uint (seed + 7).toUInt64))
        (SealedStateVar.read? (treePath 4) run.tree)
      ++ observationFailure name "the value the alias still reads" (some (.uint seed.toUInt64))
        (SealedStateVar.read? (treePath 4) keptAfter)
  return failures

/-- The flat-array update in a child with the check enabled. The update is
`Array.set!`, whose compiled implementation `lean_array_set` decides between an
update in place and a copy by the array's reference count alone and consults no
library check, so the child's evidence is that the whole case runs to completion
with the check armed; the parent's address assertion is what shows the update was
in place. -/
def updatesArrayCheckedUniqueCase : IO (Array String) := do
  let out ← launchChecked "updates-arr-unique"
  let failures :=
    markerFailure "updates-arr-checked-unique" "the child's standard output" "check-enabled=true" out.stdout
      ++ exitFailure "updates-arr-checked-unique" 0 out
      ++ markerFailure "updates-arr-checked-unique" "the child's standard output" "ok   updates-arr-unique" out.stdout
  return failures

/-- The nested-array update in a child with the check enabled must pass: the write
is the sealed class's, so both of the library's checks — the take-out's array and
the extracted inner array — are armed and neither fires. -/
def updatesNestedCheckedUniqueCase : IO (Array String) := do
  let out ← launchChecked "updates-nested-unique"
  let failures :=
    markerFailure "updates-nested-checked-unique" "the child's standard output" "check-enabled=true" out.stdout
      ++ exitFailure "updates-nested-checked-unique" 0 out
      ++ markerFailure "updates-nested-checked-unique" "the child's standard output" "ok   updates-nested-unique" out.stdout
  return failures

/-- The struct-tree update in a child with the check enabled. The tree is structs
and one word, so no array check runs on this path and the library's checks have
nothing to say about it: the child's evidence is that the whole case runs to
completion with the check armed, and the parent's spine assertion — every cell
kept its address — is what shows the write reused them. -/
def updatesTreeCheckedUniqueCase : IO (Array String) := do
  let out ← launchChecked "updates-tree-unique"
  let failures :=
    markerFailure "updates-tree-checked-unique" "the child's standard output" "check-enabled=true" out.stdout
      ++ exitFailure "updates-tree-checked-unique" 0 out
      ++ markerFailure "updates-tree-checked-unique" "the child's standard output" "ok   updates-tree-unique" out.stdout
  return failures

/-! ## The union-find

`ScidoniaExamples.UnionFind` is the example library's algorithm rather than a
single update: `find` walks to a root and halves the path on the way, `union`
links one root under the other by rank, and every write of both is
`SealedStateVar.setLeaf` at a one-step path of an `Array UInt64`, which is the
sealed class's take-out update on an exclusively owned array and a whole-buffer
copy on one a second reference reaches. The cases below drive the two shapes of
it, and they differ in one thing: what else refers to the arrays while a step's
writes run.

`uf-unique` carries the two arrays as the recursion's parameters and holds
nothing else, so every write meets the only reference to its array: both buffers
must keep their addresses, and the eight unions must leave the partition the
schedule names. `uf-shared` takes a live second reference to both arrays at every
step and reads it after that step's writes, so each step's first write replaces a
buffer with a copy: both addresses must change, the reference the writes did not
go through must still read the arrays the run started from, and the partition
must be the one `uf-unique` found — the two shapes differ in cost and not in
value. `uf-checked-shared` is the aliased run in a child with the check armed,
which must end the process naming the `Layout5` array site, that being the write
about to copy; `uf-checked-focus` is the disciplined run in the same child, which
stops at the *focus* site instead — an element of a machine-word array is not a
heap object, so the library's focus guard answers `false` for it — and that case
pins the stop, the site and the array site's absence.

The loops below are the two shapes at the level a case observes them: a step's
arrays are the recursion's parameters, and the aliased one reads each alias
through `addressIO` after the step's writes, which is both what keeps the
reference alive across them and what keeps the read from being scheduled
before them. -/

/-- A fresh rank array of `n` zeros, with room for one more, as `freshWords`
builds its arrays. The pushes are impure, so the compiler cannot make a persistent
constant of it, which matters for the same reason it does there: an array a
constant names can never be exclusively owned. -/
def freshRanks (n : Nat) : IO (Array UInt64) := do
  let mut a : Array UInt64 := Array.mkEmpty (n + 1)
  for _ in [0:n] do
    a := a.push 0
  return a

/-- Run a list of unions on the two arrays, the disciplined shape: a recursive
call carries the arrays as its parameters and nothing else refers to them, and
each step's resulting parent address is folded into the total, so that no step and
no address read is eliminated. -/
def unionStepsDisciplined : Nat → List (Nat × Nat) → Array UInt64 → Array UInt64 →
    Nat → IO (Array UInt64 × Array UInt64 × Nat)
  | _, [], parent, rank, total => return (parent, rank, total)
  | fuel, (x, y) :: rest, parent, rank, total => do
    let (parent', rank') := union fuel parent rank x y
    let here ← addressIO parent'
    unionStepsDisciplined fuel rest parent' rank' (total + here.toNat)

/-- Run the same unions with a live second reference to both arrays at every
step, read after that step's writes through `addressIO`: the reference makes the
step's first write meet a buffer another name reaches, so it replaces the buffer
with a copy, and the read is what keeps the reference alive while the writes run
and what keeps it from being scheduled before them. The values the aliases read
are folded into the total beside the addresses. -/
def unionStepsAliased : Nat → List (Nat × Nat) → Array UInt64 → Array UInt64 →
    Nat → IO (Array UInt64 × Array UInt64 × Nat)
  | _, [], parent, rank, total => return (parent, rank, total)
  | fuel, (x, y) :: rest, parent, rank, total => do
    let aliasParent := parent
    let aliasRank := rank
    let (parent', rank') := union fuel parent rank x y
    let parentHere ← addressIO aliasParent
    let rankHere ← addressIO aliasRank
    let seen := ((aliasParent[x]?).map UInt64.toNat).getD 0
      + ((aliasRank[y]?).map UInt64.toNat).getD 0
    unionStepsAliased fuel rest parent' rank'
      (total + parentHere.toNat + rankHere.toNat + seen)

/-- The partition the small schedule leaves: `0` to `3` in one set, `4` and `5`
in another, and `6` and `7` each alone. -/
def ufSmallRoots : Array Nat := #[0, 0, 0, 0, 4, 4, 6, 7]

/-- The disciplined union-find on the small schedule: both buffers keep their
addresses — every write was the take-out update of an exclusively owned array —
and the eight elements are partitioned as `ufSmallRoots` says. -/
def ufUniqueCase (name : String) : IO (Array String) := do
  let parent ← freshWords 0 smallElements
  let rank ← freshRanks smallElements
  let exclusiveBefore := exclusive parent
  let parentBefore ← addressIO parent
  let rankBefore ← addressIO rank
  let (parent', rank', total) ←
    unionStepsDisciplined smallElements smallSchedule parent rank 0
  let parentAfter ← addressIO parent'
  let rankAfter ← addressIO rank'
  let (_, roots) := representatives smallElements parent'
  IO.println s!"{name}: the parent buffer: {parentBefore}, then {parentAfter}; the rank buffer: {rankBefore}, then {rankAfter}; total={total}"
  let failures : Array String :=
    exclusiveFailure name "parent array" true exclusiveBefore
      ++ addressFailure name "the parent buffer's address" true parentBefore parentAfter
      ++ addressFailure name "the rank buffer's address" true rankBefore rankAfter
      ++ disagree name "the partition the run left" ufSmallRoots roots
      ++ disagree name "the parent array's size" smallElements parent'.size
      ++ disagree name "the rank array's size" smallElements rank'.size
  return failures

/-- The undisciplined union-find on the same eight elements and the same unions:
a live second reference to both arrays is held across every step, so each step's
first write replaces a buffer with a copy — both addresses change — the reference
the writes did not go through still reads the arrays the run started from, and the
partition is the one the disciplined run left. -/
def ufSharedCase (name : String) : IO (Array String) := do
  let parent ← freshWords 0 smallElements
  let rank ← freshRanks smallElements
  let keptParent := parent
  let keptRank := rank
  let exclusiveBefore := exclusive parent
  let parentBefore ← addressIO parent
  let rankBefore ← addressIO rank
  let (parent', rank', total) ← unionStepsAliased smallElements smallSchedule parent rank 0
  let parentAfter ← addressIO parent'
  let rankAfter ← addressIO rank'
  let keptParentAfter := keptParent
  let keptRankAfter := keptRank
  let (_, roots) := representatives smallElements parent'
  IO.println s!"{name}: the parent buffer: {parentBefore}, then {parentAfter}; the rank buffer: {rankBefore}, then {rankAfter}; total={total}"
  let failures : Array String :=
    exclusiveFailure name "parent array" false exclusiveBefore
      ++ addressFailure name "the parent buffer's address" false parentBefore parentAfter
      ++ addressFailure name "the rank buffer's address" false rankBefore rankAfter
      ++ disagree name "the partition the run left" ufSmallRoots roots
      ++ disagree name "the parent array the alias still reads" (singletons smallElements) keptParentAfter
      ++ disagree name "the rank array the alias still reads" (zeroRanks smallElements) keptRankAfter
  return failures

/-- The disciplined union-find in a child with the check enabled: what stops the
child is the library's *focus* guard, and this case pins that.

A write of `union` is `SealedStateVar.setLeaf` at `.index i .here`, and the
`Layout5` array case checks two objects: the array, before the take-out, and the
element the take-out extracted. The array is exclusively owned here, so that guard
does not fire; the extracted element is a machine word, an element of an
`Array UInt64` being a value and not a heap object, and `isExclusiveUnsafe`
answers `false` for it. So the child stops on its first write at the focus site
and not at the array site, which is what the two markers below pin — the array
marker absent, the focus marker and the report present.

That the write was in place all the same is `uf-unique`'s assertion, and the two
are the same run of the same write: with the check off, every buffer keeps its
address. The focus guard is therefore not armable on a layout whose focused
element is a scalar, and the in-place evidence for this path is the address
assertion and not a checked child. -/
def ufCheckedFocusCase : IO (Array String) := do
  let out ← launchChecked "uf-unique"
  let status :=
    if out.exitCode == 0 then
      #[s!"uf-checked-focus: the exit status: expected a nonzero status, observed {out.exitCode}"]
    else #[]
  let failures :=
    markerFailure "uf-checked-focus" "the child's standard output" "check-enabled=true" out.stdout
      ++ status
      ++ markerFailure "uf-checked-focus" "the child's standard error"
        "Scidonia.FracPerm.StateVar.Layout5.struct" out.stderr
      ++ absentMarkerFailure "uf-checked-focus" "the child's standard error"
        "Scidonia.FracPerm.StateVar.Layout5.open" out.stderr
  return failures

/-- The aliased union-find in a child with the check enabled must end the
process, naming the `Layout5` array site: the first write of the first step is
about to copy the parent buffer, which a second reference reaches. -/
def ufCheckedSharedCase : IO (Array String) := do
  let out ← launchChecked "uf-shared"
  let status :=
    if out.exitCode == 0 then
      #[s!"uf-checked-shared: the exit status: expected a nonzero status, observed {out.exitCode}"]
    else #[]
  let failures :=
    markerFailure "uf-checked-shared" "the child's standard output" "check-enabled=true" out.stdout
      ++ status
      ++ markerFailure "uf-checked-shared" "the child's standard error"
        "Scidonia.FracPerm.StateVar.Layout5.open" out.stderr
  return failures

/-! ## The benchmark

`IO.monoNanosNow` measures the two shapes of each update — on an object the caller
alone refers to and on one with a live second reference — in the same code shape
the cases above assert the addresses of. Each timed measurement runs a fixed
number of updates, so that a single clock read does not dominate it; the reported
per-operation time is the total over the repetitions divided by the operations and
the repetitions. The updates run in a recursive loop that carries the object as a
parameter, because a `for` loop body is a closure holding it, which is a second
reference: the loop the measurement runs in must not be what makes an update copy.
The numbers are printed, not asserted.

What the measurement shows is the shape of each update, and it is a measurement of
one program on one toolchain rather than a complexity theorem:

* the flat array's exclusive column stays flat as `n` grows — the write touches
  one slot of the buffer the caller owns — while its aliased column grows with
  `n`, because a shared array is replaced by a whole-buffer copy. The `extra`
  column is that copy's cost;
* the tree's two columns both walk the path, O(depth) each — the depth is `log₂` of
  the leaf count — so both grow with the depth. What the columns differ in is the
  *allocation* of the cells the update rebuilt: none for the spine when the tree is
  exclusively owned, one cell per level when it is shared, which is the `extra`
  column. That difference is small next to the walk — tens to a few hundred
  nanoseconds against columns of hundreds to thousands — and it is the noisiest
  number here, so what establishes *which* cells are reused is the address
  assertion in `updates-tree-unique` and `updates-tree-shared` beside this
  benchmark: every cell on the spine keeps its address in the first and changes in
  the second. Neither column is a constant-time operation, and nothing here measures
  the ratio of one to a logarithmic one. -/

/-- The array sizes the benchmark measures, from small to large. -/
def benchSizes : List Nat := [1000, 10000, 100000, 1000000]

/-- The tree depths the benchmark measures: a depth-`k` tree has `2^k` leaves, so
the spine the aliased update rebuilds has `k` cells. -/
def benchDepths : List Nat := [8, 12, 16, 20]

/-- The updates one timed measurement of the array benchmark runs. -/
def arrayOps : Nat := 100

/-- The timed measurements the array benchmark averages per row and shape. -/
def arrayReps : Nat := 5

/-- The updates one timed measurement of the tree benchmark runs. More than the
array's, because the tree's two shapes differ by the allocation of one cell per
level and a longer run is what keeps that difference above the noise of a single
measurement. -/
def treeOps : Nat := 200

/-- The timed measurements the tree benchmark averages per row and shape. -/
def treeReps : Nat := 11

/-- The ratio of two per-operation times, with one decimal place, and `-` when the
divisor is zero. -/
def ratioText (aliased exclusive : Nat) : String :=
  if exclusive == 0 then "-" else
    let tenths := aliased * 10 / exclusive
    s!"{tenths / 10}.{tenths % 10}"

/-- One row of the array benchmark. -/
structure ArrayBenchRow where
  /-- The array's size. -/
  size : Nat
  /-- Nanoseconds per update on an array the caller alone refers to. -/
  exclusiveNanos : Nat
  /-- Nanoseconds per update on an array with a live second reference. -/
  aliasedNanos : Nat
  /-- The difference of the two, which is what the second reference costs. -/
  extraNanos : Nat
  /-- Whether the untimed exclusive probe's update kept the buffer's address. -/
  inPlace : Bool
  /-- Whether the untimed aliased probe's update moved the buffer. -/
  copied : Bool
  /-- A sum over the addresses and values the timed updates read, so that none of
  them is eliminated. -/
  checksum : Nat

/-- The updates of one exclusive array measurement, carried out by a recursive
call that takes the array as a *parameter*: each call receives the only reference
to it, so each update writes the buffer in place. A `for` loop would hold the
array in the closure the loop body is, which is a second reference, and every
update would copy the buffer instead — the shape this benchmark is about must not
be an artifact of the loop it is measured in. The address of each result and one
of its slots are folded into the checksum. -/
def exclusiveArrayUpdates (n seed round : Nat) : Nat → Array UInt64 → Nat →
    IO (Array UInt64 × Nat)
  | 0, a, checksum => return (a, checksum)
  | ops + 1, a, checksum => do
    let a' := arrSet a (ops &&& 7) (seed + round + ops).toUInt64
    let here ← addressIO a'
    exclusiveArrayUpdates n seed round ops a' (checksum + here.toNat + a'[0]!.toNat)

/-- The timed updates of the exclusive array shape. -/
def timeExclusiveArray (n seed round : Nat) : IO (Nat × Nat) := do
  let a ← freshWords (seed + round) n
  let t0 ← IO.monoNanosNow
  let (a', checksum) ← exclusiveArrayUpdates n seed round arrayOps a 0
  let t1 ← IO.monoNanosNow
  return (t1 - t0, checksum + a'[0]!.toNat + (address a').toNat)

/-- The updates of one aliased array measurement: as the exclusive shape, with a
live second reference (`alias`) to the array held across the update, so that each
one replaces the buffer with a copy. The alias is read after the update and through
`addressIO`, for the reason the tree loops give: the read is what makes the binding
live while the update runs, and an `IO` action is what keeps it from being
scheduled before the update. -/
def aliasedArrayUpdates (n seed round : Nat) : Nat → Array UInt64 → Nat →
    IO (Array UInt64 × Nat)
  | 0, a, checksum => return (a, checksum)
  | ops + 1, a, checksum => do
    let alias := a
    let a' := arrSet a (ops &&& 7) (seed + round + ops).toUInt64
    let here ← addressIO alias
    aliasedArrayUpdates n seed round ops a' (checksum + here.toNat + alias[0]!.toNat)

/-- The timed updates of the aliased array shape. -/
def timeAliasedArray (n seed round : Nat) : IO (Nat × Nat) := do
  let a ← freshWords (seed + round) n
  let t0 ← IO.monoNanosNow
  let (a', checksum) ← aliasedArrayUpdates n seed round arrayOps a 0
  let t1 ← IO.monoNanosNow
  return (t1 - t0, checksum + a'[0]!.toNat + (address a').toNat)

/-- One row of the array benchmark: an untimed probe of each shape, which is where
the address relation comes from, then the two timed runs. -/
def benchArrayRow (n seed : Nat) : IO ArrayBenchRow := do
  let probe ← freshWords (seed + 1) n
  let probeBefore ← addressIO probe
  let probeAfter ← addressIO (arrSet probe (n / 2) seed.toUInt64)
  let aliasedProbe ← freshWords (seed + 2) n
  let keptProbe := aliasedProbe
  let aliasedBefore ← addressIO aliasedProbe
  let aliasedAfter ← addressIO (arrSet aliasedProbe (n / 2) seed.toUInt64)
  let keptProbeValue := keptProbe[n / 2]!
  let mut exclusiveTotal := 0
  let mut aliasedTotal := 0
  let mut checksum := keptProbeValue.toNat
  for r in [0:arrayReps] do
    let (exclusive, exclusiveSum) ← timeExclusiveArray n seed r
    exclusiveTotal := exclusiveTotal + exclusive
    checksum := checksum + exclusiveSum
    let (aliased, aliasedSum) ← timeAliasedArray n seed r
    aliasedTotal := aliasedTotal + aliased
    checksum := checksum + aliasedSum
  let rounds := arrayReps * arrayOps
  let exclusiveNanos := exclusiveTotal / rounds
  let aliasedNanos := aliasedTotal / rounds
  return { size := n, exclusiveNanos, aliasedNanos, extraNanos := aliasedNanos - exclusiveNanos,
           inPlace := probeBefore == probeAfter, copied := aliasedBefore != aliasedAfter,
           checksum }

/-- Print one row of the array benchmark. -/
def reportArrayBench (row : ArrayBenchRow) : IO Unit :=
  IO.println s!"bench-array: n={row.size} exclusive={row.exclusiveNanos} ns/op aliased={row.aliasedNanos} ns/op extra={row.extraNanos} ns/op ratio={ratioText row.aliasedNanos row.exclusiveNanos} in-place={row.inPlace} copies={row.copied} checksum={row.checksum}"

/-- One row of the tree benchmark. -/
structure TreeBenchRow where
  /-- The tree's depth, and so the number of cells on the spine. -/
  depth : Nat
  /-- Nanoseconds per update on a tree the caller alone refers to. -/
  exclusiveNanos : Nat
  /-- Nanoseconds per update on a tree with a live second reference. -/
  aliasedNanos : Nat
  /-- The difference of the two: what rebuilding the cells on the path costs. -/
  extraNanos : Nat
  /-- Whether the untimed exclusive probe's update kept the root's address. -/
  inPlace : Bool
  /-- Whether the untimed aliased probe's update moved the root. -/
  copied : Bool
  /-- A sum over the addresses and values the timed updates read, so that none of
  them is eliminated. -/
  checksum : Nat

/-- The updates of one exclusive tree measurement, carried out by a recursive call
that takes the tree as a *parameter*, for the reason the array loops do: a `for`
loop would hold it in a closure, which is a second reference, and each update would
then rebuild the spine instead of reusing it. -/
def exclusiveTreeUpdates (k : Nat) (seed round : UInt64) : Nat →
    Layout5.State (structTree k) → Nat → IO (Layout5.State (structTree k) × Nat)
  | 0, t, checksum => return (t, checksum)
  | ops + 1, t, checksum => do
    let t' := (treeSet k (seed + round + ops.toUInt64) t).1
    let here ← addressIO t'
    exclusiveTreeUpdates k seed round ops t' (checksum + here.toNat)

/-- The timed updates of the exclusive tree shape. -/
def timeExclusiveTree (k : Nat) (seed round : UInt64) : IO (Nat × Nat) := do
  let t := treeFilled k (seed + round)
  let t0 ← IO.monoNanosNow
  let (t', checksum) ← exclusiveTreeUpdates k seed round treeOps t 0
  let t1 ← IO.monoNanosNow
  return (t1 - t0, checksum + (address t').toNat)

/-- The updates of one aliased tree measurement: as the exclusive shape, with a
live second reference (`alias`) to the tree held across the update, so that each
one rebuilds every cell on the path.

The alias is read *after* the update and through `addressIO`, and both matter: the
read is what makes the binding live while the update runs, and it is an `IO` action
because a pure reading of the alias could be scheduled before the update, letting
the alias die first — which would show the tree as exclusively owned and hide the
copy the shape is about. -/
def aliasedTreeUpdates (k : Nat) (seed round : UInt64) : Nat →
    Layout5.State (structTree k) → Nat → IO (Layout5.State (structTree k) × Nat)
  | 0, t, checksum => return (t, checksum)
  | ops + 1, t, checksum => do
    let alias := t
    let t' := (treeSet k (seed + round + ops.toUInt64) t).1
    let here ← addressIO alias
    aliasedTreeUpdates k seed round ops t' (checksum + here.toNat)

/-- The timed updates of the aliased tree shape. -/
def timeAliasedTree (k : Nat) (seed round : UInt64) : IO (Nat × Nat) := do
  let t := treeFilled k (seed + round)
  let t0 ← IO.monoNanosNow
  let (t', checksum) ← aliasedTreeUpdates k seed round treeOps t 0
  let t1 ← IO.monoNanosNow
  return (t1 - t0, checksum + (address t').toNat)

/-- One row of the tree benchmark: an untimed probe of each shape, then the two
timed runs. -/
def benchTreeRow (k : Nat) (seed : UInt64) : IO TreeBenchRow := do
  let probe := treeFilled k (seed + 1)
  let probeBefore ← addressIO probe
  let probeAfter ← addressIO (treeSet k (seed + 7) probe).1
  let aliasedProbe := treeFilled k (seed + 2)
  let keptProbe := aliasedProbe
  let aliasedBefore ← addressIO aliasedProbe
  let aliasedAfter ← addressIO (treeSet k (seed + 7) aliasedProbe).1
  let mut checksum := 0
  match SealedStateVar.read? (treePath k) keptProbe with
  | some (.uint v) => checksum := checksum + v.toNat
  | _ => pure ()
  let mut exclusiveTotal := 0
  let mut aliasedTotal := 0
  for r in [0:treeReps] do
    let (exclusive, exclusiveSum) ← timeExclusiveTree k seed r.toUInt64
    exclusiveTotal := exclusiveTotal + exclusive
    checksum := checksum + exclusiveSum
    let (aliased, aliasedSum) ← timeAliasedTree k seed r.toUInt64
    aliasedTotal := aliasedTotal + aliased
    checksum := checksum + aliasedSum
  let rounds := treeReps * treeOps
  let exclusiveNanos := exclusiveTotal / rounds
  let aliasedNanos := aliasedTotal / rounds
  return { depth := k, exclusiveNanos, aliasedNanos, extraNanos := aliasedNanos - exclusiveNanos,
           inPlace := probeBefore == probeAfter, copied := aliasedBefore != aliasedAfter,
           checksum }

/-- Print one row of the tree benchmark. -/
def reportTreeBench (row : TreeBenchRow) : IO Unit :=
  IO.println s!"bench-tree: depth={row.depth} leaves={2 ^ row.depth} exclusive={row.exclusiveNanos} ns/op aliased={row.aliasedNanos} ns/op extra={row.extraNanos} ns/op ratio={ratioText row.aliasedNanos row.exclusiveNanos} in-place={row.inPlace} copies={row.copied} checksum={row.checksum}"

/-! ## The union-find benchmark

The union-find is measured the same way as the updates above, with one difference
that is the point of it: the unit is a *union*, and what a union costs depends on
what else refers to the arrays. Each timed measurement runs a whole sequence of
`schedule`'s unions — a value, so every row and every measurement performs the same
work — on two fresh arrays, in the recursive-parameter shape the cases above
assert the addresses of, because a `for` loop would hold the arrays in its closure
and make every write copy.

What the measurement shows is the shape of the two columns, and it is a
measurement of one program on one toolchain rather than a complexity theorem:

* the exclusive column stays near flat as `n` grows — the amortized cost of a
  union in a union-find is near-constant, and the writes it makes are the
  take-out updates of arrays nothing else refers to — while the aliased column
  grows with `n`, because a step's first write meets a buffer a second reference
  reaches and replaces it with a whole-buffer copy. The `extra` column is that
  copy's cost, and the rows' ratio is that cost against the near-constant one;
* each row's untimed probe reports which of the two the *first* union did —
  `in-place=true` for the exclusive shape, `copies=true` for the aliased one —
  and the address assertion in `uf-unique` and `uf-shared` beside this benchmark
  is the same measurement over the whole schedule. -/

/-- The union-find sizes the benchmark measures, from small to large. -/
def ufBenchSizes : List Nat := [256, 1024, 4096, 16384]

/-- The unions one timed union-find measurement at size `n` runs: a quarter of the
array. The sequence's length therefore grows with `n`, which is what makes a row's
*total* readable as a shape — the exclusive total grows with the work it does and
the aliased one with the copies — and the schedule's pairs are two elements half
the array apart, so every one of those unions links two roots of two different
sets and writes. -/
def ufOps (n : Nat) : Nat := n / 4

/-- The timed measurements the union-find benchmark averages per row and shape. -/
def ufReps : Nat := 5

/-- The timed disciplined union-find at size `n`: `ufOps n` unions of the schedule
on two fresh arrays, carried by the recursion's parameters. -/
def timeUfExclusive (n : Nat) : IO (Nat × Nat) := do
  let parent ← freshWords 0 n
  let rank ← freshRanks n
  let t0 ← IO.monoNanosNow
  let (parent', _, total) ← unionStepsDisciplined n (schedule n (ufOps n)) parent rank 0
  let t1 ← IO.monoNanosNow
  return (t1 - t0, total + ((parent'[0]?).getD 0).toNat)

/-- The timed undisciplined union-find at size `n`: as the disciplined shape, with
a live second reference to both arrays taken at every step, so each step's first
write replaces a buffer with a copy. -/
def timeUfAliased (n : Nat) : IO (Nat × Nat) := do
  let parent ← freshWords 0 n
  let rank ← freshRanks n
  let t0 ← IO.monoNanosNow
  let (parent', _, total) ← unionStepsAliased n (schedule n (ufOps n)) parent rank 0
  let t1 ← IO.monoNanosNow
  return (t1 - t0, total + ((parent'[0]?).getD 0).toNat)

/-- The timed runs of one union-find row: `reps` measurements of each shape at
size `n`, accumulating their times and the totals the runs folded their reads
into, so that no address read and no update is eliminated. -/
def timeUfRounds (n : Nat) : Nat → Nat → Nat → Nat → IO (Nat × Nat × Nat)
  | 0, exclusiveTotal, aliasedTotal, checksum => return (exclusiveTotal, aliasedTotal, checksum)
  | reps + 1, exclusiveTotal, aliasedTotal, checksum => do
    let (exclusive, exclusiveSum) ← timeUfExclusive n
    let (aliased, aliasedSum) ← timeUfAliased n
    timeUfRounds n reps (exclusiveTotal + exclusive) (aliasedTotal + aliased)
      (checksum + exclusiveSum + aliasedSum)

/-- One row of the union-find benchmark. -/
structure UnionFindBenchRow where
  /-- The number of elements the two arrays hold. -/
  size : Nat
  /-- The unions each timed run performs, which is `ufOps` at this size. -/
  ops : Nat
  /-- Mean nanoseconds the whole exclusive sequence took. -/
  exclusiveTotal : Nat
  /-- Mean nanoseconds the whole aliased sequence took. -/
  aliasedTotal : Nat
  /-- Nanoseconds per union on arrays the caller alone refers to. -/
  exclusiveNanos : Nat
  /-- Nanoseconds per union with a live second reference to both arrays. -/
  aliasedNanos : Nat
  /-- The difference of the two per-operation times, which is what the second
  reference costs. -/
  extraNanos : Nat
  /-- Whether the untimed exclusive probe's first union kept the parent buffer's
  address. -/
  inPlace : Bool
  /-- Whether the untimed aliased probe's first union moved it. -/
  copied : Bool
  /-- A sum over the addresses and values the timed runs and the probes read, so
  that none of them is eliminated. -/
  checksum : Nat

/-- One row of the union-find benchmark: an untimed probe of each shape — which is
where the address relation comes from — then the two timed runs. They time a whole
sequence of `ufOps n` unions per measurement and the row reports the sequence's
mean total beside the mean per union, since the sequence's length grows with `n`
and a total is then not comparable between rows while a per-union time is. -/
def benchUfRow (n : Nat) : IO UnionFindBenchRow := do
  let probeParent ← freshWords 0 n
  let probeRank ← freshRanks n
  let probeBefore ← addressIO probeParent
  let (probeParent', _, probeSum) ←
    unionStepsDisciplined n (schedule n 1) probeParent probeRank 0
  let probeAfter ← addressIO probeParent'
  let aliasedProbeParent ← freshWords 0 n
  let aliasedProbeRank ← freshRanks n
  let aliasedBefore ← addressIO aliasedProbeParent
  let (aliasedProbeParent', _, aliasedProbeSum) ←
    unionStepsAliased n (schedule n 1) aliasedProbeParent aliasedProbeRank 0
  let aliasedAfter ← addressIO aliasedProbeParent'
  let (exclusiveRounds, aliasedRounds, checksum) ← timeUfRounds n ufReps 0 0 0
  let ops := ufOps n
  let rounds := ufReps * ops
  let exclusiveTotal := exclusiveRounds / ufReps
  let aliasedTotal := aliasedRounds / ufReps
  let exclusiveNanos := exclusiveRounds / rounds
  let aliasedNanos := aliasedRounds / rounds
  return { size := n, ops, exclusiveTotal, aliasedTotal, exclusiveNanos, aliasedNanos,
           extraNanos := aliasedNanos - exclusiveNanos,
           inPlace := probeBefore == probeAfter, copied := aliasedBefore != aliasedAfter,
           checksum := checksum + probeSum + aliasedProbeSum }

/-- Print one row of the union-find benchmark. -/
def reportUfBench (row : UnionFindBenchRow) : IO Unit :=
  IO.println s!"bench-union-find: n={row.size} unions={row.ops} exclusive={row.exclusiveNanos} ns/op total={row.exclusiveTotal} ns aliased={row.aliasedNanos} ns/op total={row.aliasedTotal} ns extra={row.extraNanos} ns/op ratio={ratioText row.aliasedNanos row.exclusiveNanos} in-place={row.inPlace} copies={row.copied} checksum={row.checksum}"

/-- The benchmark: the two shapes of the array update at each size, the two shapes
of the tree update at each depth, and the two shapes of the union-find at each
size. The numbers are printed rather than asserted, and the run reports what it
measured rather than what it must find. -/
def runBenchmark (seed : Nat) : IO Unit := do
  IO.println "bench: the array update, exclusive (the caller alone refers to the array) against aliased (a live second reference)"
  for n in benchSizes do
    reportArrayBench (← benchArrayRow n seed)
  IO.println "bench: the tree update, exclusive against aliased; the walk is in both columns, so the extra is the allocation of the cells the update rebuilt"
  for k in benchDepths do
    reportTreeBench (← benchTreeRow k seed.toUInt64)
  IO.println "bench: the union-find, exclusive against aliased; a union's writes are take-out updates of the two arrays, and the aliased shape copies a buffer at every step"
  for n in ufBenchSizes do
    reportUfBench (← benchUfRow n)
  IO.println "bench: per-operation times are means over arrayOps (treeOps, ufOps) updates and arrayReps (treeReps, ufReps) measurements; a measurement of this program on this toolchain, not a complexity theorem"

/-! ## The entry point -/


/-- Print one case's verdict and count it. -/
def report (name : String) (failures : Array String) : IO UInt32 := do
  if failures.isEmpty then
    IO.println s!"ok   {name}"
    return 0
  else
    IO.println s!"FAIL {name}"
    for line in failures do
      IO.eprintln s!"     {line}"
    return 1

/-- The parent's run: every case except the children's, then the children. -/
def runAll : IO UInt32 := do
  if inplaceCheckEnabled then
    IO.eprintln "inplace: SCIDONIA_CHECK_INPLACE is set; this program runs the shared and literal cases unchecked and checks the abort in its children, so unset the variable"
    return 2
  -- A value the compiler cannot know, so that the literal case's write runs.
  let seed := (← IO.monoMsNow) % 97 + 1
  -- The structured cases start from the same kind of run-time value, so that
  -- `Array.replicate` cannot become a persistent constant on their path.
  let fill : UInt64 := (seed % 89 + 1).toUInt64
  let cases : Array (String × Array String) := #[
    ("p1-unique", ← uniqueCase "p1-unique"),
    ("p2-unique", ← readersCase "p2-unique"),
    ("shared-copies", ← sharedCase "shared-copies"),
    ("literal-copies", ← literalCase "literal-copies" seed),
    ("counter-unique", ← counterUniqueCase "counter-unique"),
    ("counter-shared-log", ← counterSharedCase "counter-shared-log"),
    ("counter-shared-log-bump", ← counterSharedBumpCase "counter-shared-log-bump"),
    ("structured-unique", ← structuredUniqueCase "structured-unique" fill),
    ("structured-closure", ← structuredClosureCase "structured-closure" fill),
    ("layout5-unique", ← layout5UniqueCase "layout5-unique" seed),
    ("layout5-right", ← layout5RightCase "layout5-right" seed),
    ("layout5-last", ← layout5LastCase "layout5-last" seed),
    ("layout5-out-of-bounds", ← layout5BadCase "layout5-out-of-bounds" seed),
    ("layout5-shared-copies", ← layout5AliasedCase "layout5-shared-copies" seed),
    ("layout5-nest", ← layout5NestCase "layout5-nest" seed),
    ("layout5-nest-aliased", ← layout5NestAliasedCase "layout5-nest-aliased" seed),
    ("sealed-unique", ← sealedUniqueCase "sealed-unique" seed),
    ("checked-abort", ← checkedAbortCase),
    ("checked-unique", ← checkedUniqueCase),
    ("counter-checked-unique", ← counterCheckedUniqueCase),
    ("counter-checked-shared-log", ← counterCheckedAbortCase),
    ("counter-checked-shared-log-bump", ← counterCheckedBumpCase),
    ("structured-checked-unique", ← checkedStructuredUniqueCase),
    ("structured-checked-closure", ← checkedStructuredClosureCase),
    ("layout5-checked-unique", ← checkedLayout5UniqueCase),
    ("layout5-checked-shared", ← checkedLayout5AliasedCase),
    ("layout5-checked-nest", ← checkedLayout5NestCase),
    ("layout5-checked-nest-shared", ← checkedLayout5NestAliasedCase),
    ("sealed-checked-unique", ← checkedSealedUniqueCase),
    ("updates-arr-unique", ← updatesArrayUniqueCase "updates-arr-unique" seed),
    ("updates-arr-shared", ← updatesArraySharedCase "updates-arr-shared" seed),
    ("updates-nested-unique", ← updatesNestedUniqueCase "updates-nested-unique" seed),
    ("updates-nested-shared", ← updatesNestedSharedCase "updates-nested-shared" seed),
    ("updates-tree-unique", ← updatesTreeUniqueCase "updates-tree-unique" seed),
    ("updates-tree-shared", ← updatesTreeSharedCase "updates-tree-shared" seed),
    ("updates-arr-checked-unique", ← updatesArrayCheckedUniqueCase),
    ("updates-nested-checked-unique", ← updatesNestedCheckedUniqueCase),
    ("updates-tree-checked-unique", ← updatesTreeCheckedUniqueCase),
    ("uf-unique", ← ufUniqueCase "uf-unique"),
    ("uf-shared", ← ufSharedCase "uf-shared"),
    ("uf-checked-focus", ← ufCheckedFocusCase),
    ("uf-checked-shared", ← ufCheckedSharedCase)
  ]
  let mut status : UInt32 := 0
  for (name, failures) in cases do
    status := max status (← report name failures)
  -- The benchmark prints its measurements; it reports no failures of its own.
  runBenchmark seed
  return status

/-- The child's run of one case: report the switch, then the case. -/
def runChild (command : String) : IO UInt32 := do
  IO.println s!"check-enabled={inplaceCheckEnabled}"
  let seed := (← IO.monoMsNow) % 97 + 1
  let fill : UInt64 := ((← IO.monoMsNow) % 89 + 1).toUInt64
  match command with
  | "unique" => report "unique" (← uniqueCase "unique")
  | "shared" => report "shared" (← sharedCase "shared")
  | "counter-unique" => report "counter-unique" (← counterUniqueCase "counter-unique")
  | "counter-shared" => report "counter-shared" (← counterSharedCase "counter-shared")
  | "counter-shared-bump" => report "counter-shared-bump" (← counterSharedBumpCase "counter-shared-bump")
  | "structured-unique" => report "structured-unique" (← structuredUniqueCase "structured-unique" fill)
  | "structured-closure" => report "structured-closure" (← structuredClosureCase "structured-closure" fill)
  | "layout5-unique" => report "layout5-unique" (← layout5UniqueCase "layout5-unique" seed)
  | "layout5-shared" => report "layout5-shared" (← layout5AliasedCase "layout5-shared" seed)
  | "layout5-nest" => report "layout5-nest" (← layout5NestCase "layout5-nest" seed)
  | "layout5-nest-shared" => report "layout5-nest-shared" (← layout5NestAliasedCase "layout5-nest-shared" seed)
  | "sealed-unique" => report "sealed-unique" (← sealedUniqueCase "sealed-unique" seed)
  | "updates-arr-unique" => report "updates-arr-unique" (← updatesArrayUniqueCase "updates-arr-unique" seed)
  | "updates-arr-shared" => report "updates-arr-shared" (← updatesArraySharedCase "updates-arr-shared" seed)
  | "updates-nested-unique" => report "updates-nested-unique" (← updatesNestedUniqueCase "updates-nested-unique" seed)
  | "updates-nested-shared" => report "updates-nested-shared" (← updatesNestedSharedCase "updates-nested-shared" seed)
  | "updates-tree-unique" => report "updates-tree-unique" (← updatesTreeUniqueCase "updates-tree-unique" seed)
  | "updates-tree-shared" => report "updates-tree-shared" (← updatesTreeSharedCase "updates-tree-shared" seed)
  | "uf-unique" => report "uf-unique" (← ufUniqueCase "uf-unique")
  | "uf-shared" => report "uf-shared" (← ufSharedCase "uf-shared")
  | _ => do
    IO.eprintln s!"inplace: unknown command {command}"
    return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => runAll
  | [command] => runChild command
  | _ => do
    IO.eprintln "usage: inplace [unique|shared|counter-unique|counter-shared|counter-shared-bump|structured-unique|structured-closure|layout5-unique|layout5-shared|layout5-nest|layout5-nest-shared|sealed-unique|updates-arr-unique|updates-arr-shared|updates-nested-unique|updates-nested-shared|updates-tree-unique|updates-tree-shared|uf-unique|uf-shared]"
    return 2
