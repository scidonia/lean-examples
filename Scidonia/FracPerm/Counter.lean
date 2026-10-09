/-
A worked second instance of `Scidonia.FracPerm.FracObject`: a counter with a
`Nat` field and an `Array Nat` field.

It is here to be the interface's own second example, and to be the case its
checks run against: the counter's mutable state is partly a field of a larger
object, so it is the case where the check has something to say that a check of
the whole object cannot. A live reference to `s.log` outside the counter
leaves the counter itself exclusively owned while making the log shared; a
check of the counter alone passes, and `record`'s push copies the log instead
of appending to it.

The counter also shows both rules of the interface in a worked form: `observe`
returns the count or one element of the log, and so hands back neither the
counter nor the log, the parts a write updates in place; and `update` writes
through `{ s with … }` and so keeps no old part of the counter alive.
-/
import Scidonia.FracPerm.Hoare

namespace Scidonia.FracPerm

/-- A counter: how many times it has been bumped, and the values recorded in
it. -/
structure Counter where
  /-- The counter's count: how many times it was bumped. -/
  hits : Nat
  /-- The array field: the recorded values, in order. -/
  log : Array Nat

namespace Counter

/-- The counter's read operations. -/
inductive ReadOp where
  /-- Read the count. -/
  | hits
  /-- Read the log's entry `i`. -/
  | entry (i : Nat)

/-- What each read operation yields. -/
def Result : ReadOp → Type
  | .hits => Nat
  | .entry _ => Option Nat

/-- The counter's write operations. -/
inductive WriteOp where
  /-- Add one to the count. -/
  | bump
  /-- Push `x` onto the log. -/
  | record (x : Nat)

/-- Perform a read operation. Neither result is a reference to a part of the
counter that a write updates in place: `hits` yields the count, `entry i`
yields one element of the log, and neither is the counter or the log itself.
A result that named the log — or the counter — would be an alias whose next
write copies it. Values that no write mutates in place are a different matter:
a `Nat` may itself be a heap object, and an element's value may be shared, and
that is harmless and expected. -/
def observe : (o : ReadOp) → Counter → Result o
  | .hits, s => s.hits
  | .entry i, s => s.log[i]?

/-- Perform a write operation in place. `{ s with … }` writes the one field the
operation names and leaves the other in the counter, so an update in place
keeps both of the counter's addresses. -/
def update : WriteOp → Counter → Counter
  | .bump, s => { s with hits := s.hits + 1 }
  | .record x, s => { s with log := s.log.push x }

/-- The compiled counter check. It is not the check of the counter alone: the
log is a reference-counted field of the counter, and a reference to it held
outside the counter leaves the counter itself exclusive while making the field
shared, so a check of the counter would pass and the copy would be silent.

The operation decides which fields are checked. `bump` writes `hits` alone, so
a shared log is no reason to abort it — an abort must mean that this write is
about to copy, not merely that some part of the state is shared. `record`
writes the log, so there the log's ownership is what the check is for.

The check receives the write site, the operation and the state. The site is
handed to it as a string, so the report names the field rather than a line of
code. -/
@[never_extract, noinline]
unsafe def checkImpl (site : @& String) (o : WriteOp) (s : Counter) : Counter :=
  if inplaceCheckEnabled then
    if !isExclusiveUnsafe s then
      reportNotExclusive site "the Counter is not exclusively owned" s
    else
      match o with
      | .bump => s
      | .record _ =>
        if isExclusiveUnsafe s.log then s
        else reportNotExclusive site "the Counter's log field is not exclusively owned" s
  else s

set_option linter.unusedVariables.funArgs false in
/-- The counter's check, the identity in the logic: its compiled form
`checkImpl` is the checking function. -/
@[implemented_by checkImpl]
def check (site : @& String) (o : WriteOp) (s : Counter) : Counter := s

/-- The counter as a `FracObject`. Its `check` is its own, so `write` checks
the counter's mutable parts and not only the counter. -/
instance instFracObjectCounter : FracObject Counter Counter.ReadOp Counter.WriteOp where
  Result := Result
  observe := observe
  update := update
  check := fun site o s => check site o s
  check_eq := fun _ _ _ => rfl

end Counter

end Scidonia.FracPerm
