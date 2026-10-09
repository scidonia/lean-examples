/-
An optional run-time check that a `write` updates the array in place.

The interface is specified over values: `write`'s postcondition is
`a' = a.set! i v` whatever the runtime does. Compiled, a program threads one
reference-counted `Array α`, and `Array.set!` updates that object in place
exactly when the reference is exclusive; a shared array, or a persistent one
such as a literal, is copied instead. A copy costs a whole-array allocation,
and the specification cannot see the difference. `assertExclusive` makes the
difference observable: it is the identity in the logic, so no specification
mentions it, and it can abort a compiled program that would copy.

The check is off unless `SCIDONIA_CHECK_INPLACE` is `1` in the process
environment. The variable is read once, when the module is initialized, into a
global the check branches on, so no write reads the environment — a write calls
the check, which loads that global and branches.

Sharing the array is legal — it costs a copy, it is not an error. The check
reports only that a copy happened where the interface's client expected an
update in place, and it reports it by terminating the process, because a
program that keeps running after a silently copied write has lost the property
the check was asked for.
-/
namespace Scidonia.FracPerm

/-- The check's switch, read once from the process environment at
initialization. A client reads `inplaceCheckEnabled` rather than the variable,
and the compiled check reads it as a global, so no write touches the
environment. -/
initialize inplaceCheck : Bool ←
  return ((← IO.getEnv "SCIDONIA_CHECK_INPLACE") == some "1")

/-- Whether the in-place check is enabled in this process. -/
def inplaceCheckEnabled : Bool := inplaceCheck

/-- The report for a write that would copy: the site it happened at and the
size of the array that was not exclusively owned. -/
def inplaceReport (site : String) (size : Nat) : String :=
  let head := s!"in-place check: {site} received an array of size {size}"
  head ++ " that is not exclusively owned, so the write copies it instead of updating it in place"

/-- Print the report on standard error and terminate the process with a
nonzero status. The exit does not depend on the message: a failed write to
standard error is caught, and the process ends whether or not the message
reached the stream, so no path here hands the array back for the write to
continue with.

Both match arms are unreachable — the print is caught, and the exit after it
does not return — and each holds a panic rather than the array. They are
deliberately different terms: were they the same, the compiler would be free to
drop the print, and the exit, along with the match.

The `pure a` that types the action at the array is load-bearing. It is what
makes `a` a parameter this function may hand back, and so what keeps the
parameter owned; taken borrowed, it would make the caller's array borrowed too,
and the write would give `lean_array_set` a second reference and copy. -/
unsafe def reportNotExclusive {α : Type} (site : @& String) (a : Array α) : Array α :=
  match unsafeIO (do
      try IO.eprintln (inplaceReport site a.size) catch _ => pure ()
      IO.Process.exit 1
      pure a) with
  | .ok _ => panic "Scidonia.FracPerm: the in-place check did not end the process"
  | .error _ => panic "Scidonia.FracPerm: the in-place check could not report and did not end the process"

/-- The compiled `assertExclusive`: when the check is enabled, terminate
unless the array is exclusively owned, and otherwise hand the array straight
back. -/
@[never_extract, noinline]
unsafe def assertExclusiveImpl (site : @& String) (a : Array α) : Array α :=
  if inplaceCheckEnabled then
    if isExclusiveUnsafe a then a else reportNotExclusive site a
  else a

set_option linter.unusedVariables.funArgs false in
/-- The identity in the logic — `assertExclusive site a = a` — so no
specification or proof mentions it. Its compiled implementation
`assertExclusiveImpl` checks that `a` is exclusively owned, so that a client
of `write` can ask for the copy to be turned into a loud failure rather than a
silent one.

The array is written at `Type`, as `HArr`'s parameter is: the check makes the
program exit, `IO` is monomorphic, and the interface's `Array α` never leaves
`Type` anyway. -/
@[implemented_by assertExclusiveImpl]
def assertExclusive {α : Type} (site : @& String) (a : Array α) : Array α := a

end Scidonia.FracPerm
