/-
An optional run-time check that a `write` updates its object in place.

The interface is specified over values: `write`'s postcondition is
`s' = update o s` whatever the runtime does. Compiled, a program threads one
reference-counted object, and an in-place update mutates that object exactly
when the reference is exclusive; a shared object, or a persistent one such as
a literal, is replaced by a copy instead. A copy costs a whole-object
allocation, and the specification cannot see the difference. `assertExclusive`
makes the difference observable: it is the identity in the logic, so no
specification mentions it, and it can abort a compiled program that would copy.

The check is off unless `SCIDONIA_CHECK_INPLACE` is `1` in the process
environment. The variable is read once, when the module is initialized, into a
global the check branches on, so no write reads the environment — a write calls
the check, which loads that global and branches.

Sharing an object is legal — it costs a copy, it is not an error. The check
reports only that a copy happened where the interface's client expected an
update in place, and it reports it by terminating the process, because a
program that keeps running after a silently copied write has lost the property
the check was asked for.

The check is a parameter of the object: `Scidonia.FracPerm.FracObject.check`
defaults to `assertExclusive`, and an instance whose mutable state is a field
of a larger object replaces it with a check of that field, which is what makes
the difference observable for the field rather than only for the object.
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

/-- The report for an update that would copy: the site it happened at, and what
that site found that is not exclusively owned. -/
def inplaceReport (site detail : String) : String :=
  s!"in-place check: {site}: {detail}, so the update copies it instead of updating it in place"

/-- Print the report on standard error and terminate the process with a
nonzero status. The exit does not depend on the message: a failed write to
standard error is caught, and the process ends whether or not the message
reached the stream, so no path here hands the state back for the update to
continue with.

The action hands the state back (`pure s`), and the `.ok` arm returns what the
action produced. That is load-bearing: it is what makes `s` a parameter this
function may hand back, and so what keeps the parameter owned. Taken borrowed,
it would make the caller's state borrowed too, and the update would give the
runtime a second reference and copy.

Both match arms are unreachable — the print is caught, and the exit after it
does not return — and they are deliberately different terms, so that the
compiler cannot merge them and drop the report, the exit and the match along
with it. The `.error` arm has no state to hand back; since it cannot be
reached, it casts the unit value rather than demanding that every object's
state type be inhabited, which `panic` would. -/
unsafe def reportNotExclusive {σ : Type} (site : @& String) (detail : String) (s : σ) : σ :=
  match unsafeIO (do
      try IO.eprintln (inplaceReport site detail) catch _ => pure ()
      IO.Process.exit 1
      pure s) with
  | .ok x => x
  | .error _ => unsafeCast ()

/-- The compiled `assertExclusive`: when the check is enabled, terminate unless
the object is exclusively owned, and otherwise hand the object straight back. -/
@[never_extract, noinline]
unsafe def assertExclusiveImpl {σ : Type} (site : @& String) (s : σ) : σ :=
  if inplaceCheckEnabled then
    if isExclusiveUnsafe s then s else reportNotExclusive site "an object that is not exclusively owned" s
  else s

set_option linter.unusedVariables.funArgs false in
/-- The identity in the logic — `assertExclusive site s = s` — so no
specification or proof mentions it. Its compiled implementation
`assertExclusiveImpl` checks that `s` is exclusively owned, so that a client of
`write` can ask for the copy to be turned into a loud failure rather than a
silent one. It is the default `check` of an object: for an object whose mutable
state is a field, an instance replaces it with a check of that field, and
`assertExclusive` on the field's own type is what that check calls.

The state is written at `Type`, as `HSt`'s parameter is: the check makes the
program exit, `IO` is monomorphic, and the interface's `σ` never leaves `Type`
anyway. -/
@[implemented_by assertExclusiveImpl]
def assertExclusive {σ : Type} (site : @& String) (s : σ) : σ := s

/-- The compiled `assertExclusiveArray`: as `assertExclusiveImpl`, and it also
reports the array's size, the one thing an array can say about an update that
would copy it that a general object cannot. -/
@[never_extract, noinline]
unsafe def assertExclusiveArrayImpl {α : Type} (site : @& String) (a : Array α) : Array α :=
  if inplaceCheckEnabled then
    if isExclusiveUnsafe a then a
    else reportNotExclusive site s!"an array of size {a.size} that is not exclusively owned" a
  else a

set_option linter.unusedVariables.funArgs false in
/-- The array's check: the identity in the logic, like `assertExclusive`, with a
compiled implementation that names the array's size in its report. -/
@[implemented_by assertExclusiveArrayImpl]
def assertExclusiveArray {α : Type} (site : @& String) (a : Array α) : Array α := a

end Scidonia.FracPerm
