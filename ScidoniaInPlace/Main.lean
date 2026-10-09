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
* child processes launched as `lake exe inplace unique|shared|counter-…` with
  `SCIDONIA_CHECK_INPLACE=1`. The shared cases must exit nonzero with the
  write site named on standard error, the unique cases must exit zero having
  reported the check enabled, which is what shows the check was armed and did
  not fire on an update in place. The counter's `bump` writes only `hits`, so
  the child that bumps a counter with a shared log must exit zero too: the
  counter's check is told the operation, and an abort must mean that this
  write is about to copy, not merely that some part of the object is shared.
-/
import Scidonia.FracPerm

open Scidonia.FracPerm
open Scidonia.FracPerm.HSt

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
  let cases : Array (String × Array String) := #[
    ("p1-unique", ← uniqueCase "p1-unique"),
    ("p2-unique", ← readersCase "p2-unique"),
    ("shared-copies", ← sharedCase "shared-copies"),
    ("literal-copies", ← literalCase "literal-copies" seed),
    ("counter-unique", ← counterUniqueCase "counter-unique"),
    ("counter-shared-log", ← counterSharedCase "counter-shared-log"),
    ("counter-shared-log-bump", ← counterSharedBumpCase "counter-shared-log-bump"),
    ("checked-abort", ← checkedAbortCase),
    ("checked-unique", ← checkedUniqueCase),
    ("counter-checked-unique", ← counterCheckedUniqueCase),
    ("counter-checked-shared-log", ← counterCheckedAbortCase),
    ("counter-checked-shared-log-bump", ← counterCheckedBumpCase)
  ]
  let mut status : UInt32 := 0
  for (name, failures) in cases do
    status := max status (← report name failures)
  return status

/-- The child's run of one case: report the switch, then the case. -/
def runChild (command : String) : IO UInt32 := do
  IO.println s!"check-enabled={inplaceCheckEnabled}"
  match command with
  | "unique" => report "unique" (← uniqueCase "unique")
  | "shared" => report "shared" (← sharedCase "shared")
  | "counter-unique" => report "counter-unique" (← counterUniqueCase "counter-unique")
  | "counter-shared" => report "counter-shared" (← counterSharedCase "counter-shared")
  | "counter-shared-bump" => report "counter-shared-bump" (← counterSharedBumpCase "counter-shared-bump")
  | _ => do
    IO.eprintln s!"inplace: unknown command {command}"
    return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => runAll
  | [command] => runChild command
  | _ => do
    IO.eprintln "usage: inplace [unique|shared|counter-unique|counter-shared|counter-shared-bump]"
    return 2
