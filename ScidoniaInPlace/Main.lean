/-
The in-place check of `Scidonia.FracPerm` exercised as a running program.

A proved specification cannot see whether `write` updated the array in place
or replaced it with a copy: `assertExclusive` is the identity in the logic.
This program observes the difference at run time, through the pointer and the
reference count of the array the interface actually threads.

Run it with `lake exe inplace`; it exits `0` only when every case below holds,
and each case that fails names what it expected and what it saw. It must run
with the check off — it runs the shared and the literal case itself, and those
must copy — and the two child processes are what carry
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
* two child processes launched as `lake exe inplace unique|shared` with
  `SCIDONIA_CHECK_INPLACE=1`: the shared case must exit nonzero with the write
  site named on standard error, and the unique case must exit zero having
  reported the check enabled, which is what shows the check was armed and did
  not fire on an update in place.
-/
import Scidonia.FracPerm

open Scidonia.FracPerm
open Scidonia.FracPerm.HArr

/-! ## The programs

Two programs in the shape the interface's own checks use: one write, a read
lent out under a token, the fraction returned, and a second write; and one
write, three readers holding `1/2`, `1/4` and `1/4` at once, and a second
write. -/

/-- The P1 program: write, lend out a third and two thirds, read with the
third, give both back, and write again. -/
def p1 :=
  write (α := Nat) 0 7 >>>= fun _ =>
  acquire 0 (1 / 3) >>>= fun t₁ =>
  acquire 1 (2 / 3) >>>= fun t₂ =>
  read t₁ 0 >>>= fun v =>
  release t₁ >>>= fun _ =>
  release t₂ >>>= fun _ =>
  write 1 9 >>>= fun _ =>
  ret v

/-- The readers program: write, lend out a half and two quarters, read with
each token, give all three back, and write again. -/
def p2 :=
  write (α := Nat) 0 1 >>>= fun _ =>
  acquire 0 (1 / 2) >>>= fun t₁ =>
  acquire 1 (1 / 4) >>>= fun t₂ =>
  acquire 2 (1 / 4) >>>= fun t₃ =>
  read t₁ 1 >>>= fun v₁ =>
  read t₂ 2 >>>= fun v₂ =>
  read t₃ 3 >>>= fun v₃ =>
  release t₁ >>>= fun _ =>
  release t₂ >>>= fun _ =>
  release t₃ >>>= fun _ =>
  write 1 2 >>>= fun _ =>
  ret (v₁, v₂, v₃)

/-! ## Observing a run

`exclusive` and `address` read the array borrowed — the `@&` is what keeps
them from taking a reference of their own — so `exclusive` answers for the
caller's reference and the address is the object the program is handed. -/

/-- Whether `a` is exclusively owned: a single reference to a non-persistent
object. -/
def exclusive (a : @& Array Nat) : Bool := unsafe isExclusiveUnsafe a

/-- The address `a` lives at. -/
def address (a : @& Array Nat) : USize := unsafe ptrAddrUnsafe a

/-- What one run of a program on an array leaves to check: whether the array
was exclusively owned and where it lived before the run, where the program's
array lives after it, and what the program returned. -/
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
def observe {β : Type} {P : Pre Nat} {Q : Post Nat β}
    (prog : HArr Nat P β Q) (a : Array Nat) (hp : P [] a)
    (hq : ∀ b l' a', Q [] a b l' a' → l'.held = 1) : Run β :=
  let exclusiveBefore := exclusive a
  let addressBefore := address a
  let r := prog.exec a hp hq
  let addressAfter := address r.2
  { exclusiveBefore, addressBefore, addressAfter, value := r.1, array := r.2 }

/-- A fresh array of `n` consecutive values from `seed`. The pushes are
impure, so the compiler cannot merge this expression with another one and the
caller holds the single reference to the result. -/
def freshArray (seed n : Nat) : IO (Array Nat) := do
  let mut a : Array Nat := #[]
  for i in [0:n] do
    a := a.push (seed + i)
  return a

/-! ## Turning a run into failures

Each helper returns the lines describing what did not hold; an empty array is
a case that passed. -/

/-- `#[]` when the two values agree, and one line naming the case, what was
expected and what was observed otherwise. -/
def disagree {α : Type} [BEq α] [Repr α] (name label : String)
    (expected observed : α) : Array String :=
  if expected == observed then #[] else
    #[s!"{name}: {label}: expected {repr expected}, observed {repr observed}"]

/-- `#[]` when the array was exclusively owned, or not, as the case expects,
and one line naming the case, the expectation and the observation otherwise. -/
def exclusiveFailure (name : String) (expected : Bool) (run : Run β) : Array String :=
  if run.exclusiveBefore == expected then #[] else
    #[s!"{name}: the array handed to the program: expected exclusively owned = {expected}, observed exclusively owned = {run.exclusiveBefore}"]

/-- `#[]` when the array was left at the expected address, and one line naming
the case, the expectation and both addresses otherwise. -/
def addressFailure (name : String) (expectedSame : Bool) (run : Run β) : Array String :=
  if (run.addressBefore == run.addressAfter) == expectedSame then #[] else
    let expected :=
      if expectedSame then "the same address, an update in place"
      else "a different address, a copy"
    #[s!"{name}: the address the array was left at: expected {expected}, observed {run.addressBefore}, then {run.addressAfter}"]

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
  exclusiveFailure name true run ++
  addressFailure name true run ++
  disagree name "the value the program returned" expectedValue run.value ++
  disagree name "the array the program left behind" expectedArray run.array

/-- The assertions an array with a live second reference must satisfy: it was
not exclusive, the write copied rather than updated in place, and the
reference that was not written through kept its values. -/
def copyFailures {β : Type} [BEq β] [Repr β] (name : String) (run : Run β)
    (secondReference : Array Nat) (expectedSecondReference : Array Nat)
    (expectedValue : β) (expectedArray : Array Nat) : Array String :=
  exclusiveFailure name false run ++
  addressFailure name false run ++
  disagree name "the array the second reference still reads" expectedSecondReference secondReference ++
  disagree name "the value the program returned" expectedValue run.value ++
  disagree name "the array the program left behind" expectedArray run.array

/-! ## The cases

Each case builds its array, runs its program, and reports the failures. -/

/-- The P1 case on an array the caller alone refers to. -/
def uniqueCase (name : String) : IO (Array String) := do
  let fresh ← freshArray 10 4
  return inPlaceFailures name (observe p1 fresh (by harr_vc) (by harr_vc)) (some 7) #[7, 9, 12, 13]

/-- The readers case on an array the caller alone refers to. -/
def readersCase (name : String) : IO (Array String) := do
  let fresh ← freshArray 10 4
  return inPlaceFailures name (observe p2 fresh (by harr_vc) (by harr_vc))
    (some 11, some 12, some 13) #[1, 2, 12, 13]

/-- The P1 case on an array a second binding still refers to. `kept` is read
after the run, so the array it names stays alive throughout and the program's
reference cannot be the only one. -/
def sharedCase (name : String) : IO (Array String) := do
  let shared ← freshArray 10 4
  let kept := shared
  let run := observe p1 shared (by harr_vc) (by harr_vc)
  return copyFailures name run kept #[10, 11, 12, 13] (some 7) #[7, 9, 12, 13]

/-- The literal case: `#[10, 11, 12, 13]` is a closed term, so the compiler
emits it once as a persistent object — a constant with no reference count —
and every use of it names that one object, which can never be exclusively
owned. The value written comes from the caller, so this run is not folded
away at compile time. The array the program leaves behind is a fresh copy with
the written value, and the literal the program was handed is untouched. -/
def literalCase (name : String) (seed : Nat) : IO (Array String) := do
  let literal : Array Nat := #[10, 11, 12, 13]
  let prog := write (α := Nat) 0 seed >>>= fun _ => ret seed
  let run := observe prog literal (by harr_vc) (by harr_vc)
  let failures : Array String :=
    exclusiveFailure name false run
      ++ addressFailure name false run
      ++ disagree name "the value the program returned" seed run.value
      ++ disagree name "the array the program left behind" #[seed, 11, 12, 13] run.array
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
      ++ markerFailure "checked-abort" "the child's standard error" "Scidonia.FracPerm.HArr.write" out.stderr
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
    ("checked-abort", ← checkedAbortCase),
    ("checked-unique", ← checkedUniqueCase)
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
  | _ => do
    IO.eprintln s!"inplace: unknown command {command}"
    return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => runAll
  | [command] => runChild command
  | _ => do
    IO.eprintln "usage: inplace [unique|shared]"
    return 2
