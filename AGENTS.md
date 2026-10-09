# Scidonia (Lean)

Lean 4 development of the Scidonia proof machinery: the cyclic-proof port under
`Scidonia/Cyclic/` (see `README_LEAN_CYCLIC.md`) and the fractional-permission
object interface under `Scidonia/FracPerm/`.

## Toolchain

Lean `v4.35.0-rc3` and Lake come from the flake's dev shell. There is no Mathlib
dependency; the only package is `std`. Run every toolchain command through the
shell, so that the command brings its own environment rather than depending on an
activated shell:

```bash
nix develop -c lake build
```

## Build and check

- `nix develop -c lake build` builds the default targets: the `Scidonia`
  library and the `scidonia` executable.
- `nix develop -c lake build ScidoniaTest` builds the check library.
- `nix develop -c lake build ScidoniaExamples` builds the examples library.
- `nix develop -c lake build inplace` builds the run-time harness of the
  in-place check.
- `nix develop -c lake exe inplace` runs that harness. It exits `0` only when
  every case it checks holds, and it names what it expected and what it saw
  for each case that fails.

All of them must succeed. New work adds no `sorry` and no `native_decide`. The
one `sorry` in `Scidonia/Cyclic/Syntax/StrictPos.lean` is pre-existing and is
not a precedent.

## Checks

The compile-time checks live in the check library:

- `ScidoniaTest/FracPerm.lean` checks `Scidonia.FracPerm` from outside the
  module, so it sees exactly what a client of the interface sees. The check
  library is separate from `Scidonia` for that reason.
- A check is a theorem, a `#guard` on an evaluated result, or a `#guard_msgs`
  around a command whose elaboration must fail. `#guard_msgs` pins the expected
  message, so such a check fails both when the command starts being accepted and
  when it starts failing for a different reason.
- Every rule of an interface gets an affirmative control — a program that
  elaborates and runs — paired with negative checks. A negative check is a
  theorem stating that the specific obligation of a specific program is false:
  a proposition about `HSt.pre` or about the closing condition of `HSt.exec`,
  not merely a tactic that is expected to fail.
- `ScidoniaTest.lean` is the root module of the check library. Lake needs it
  because a library's root is the module named after the library, and the file
  must import the modules that carry the checks.

A program names its object once, on the first primitive that is a read or a
write, and the rest of the program is typed from it: the interface has more
than one object and no way to guess which one a bare `read` or `write` is for.
The array's checks keep the meaning they had when the interface was the
array's; the counter's checks — C1, and the examples' C1 and C2 — are the same
obligations against the second instance, a count and a log.

The in-place check of `Scidonia.FracPerm` is checked by running rather than by
elaboration: `nix develop -c lake exe inplace` runs `ScidoniaInPlace/Main.lean`,
which observes the address and the reference count of the objects the interface
threads and relaunches itself with `SCIDONIA_CHECK_INPLACE=1` to check that a
write which would copy terminates the process. The file documents its cases:
the array's unique, shared and literal runs; the counter's, whose mutable state
is a field of a structure, so a live reference to `log` held outside the
counter shares the field while leaving the counter itself exclusive; and the
children, which show the check firing for `record` and *not* firing for `bump`,
whose write does not touch the log.

## Writing an instance

An object joins the interface by an instance of `FracObject`: the instance
names the object's read and write operation types and gives `observe`, `update`
and `check`. Two of the rules are the instance's rather than the interface's,
because they are about how Lean's values are represented and not about their
mathematics:

- `observe` must not return a reference to a part of the state that some write
  updates in place. A read that hands back the array field of a structure
  leaves an alias behind, and the next `update` of that field copies it. No
  permission can prevent that: the permissions speak about the ledger, not
  about the references. Sharing values that no write mutates in place — a
  `Nat`, or an element's own value — is harmless and expected; what a read's
  result must not name is the state's mutable parts.
- `update` must not keep an old part of the state alive. `{ s with f := … }`
  writes the one field it names; rebuilding the state around copies of its
  other parts makes the next update copy them.

`withRead n q body` is the leak-free way to read. It lends the fraction, runs
`body` with the token, gives the fraction back and returns the body's result,
so there is no `release` for a client to forget, and a body that returns a
token hands back a dead name.

`check` is what `write` runs on the operation and the state before `update`. It
is the identity in the logic — an instance whose `check` is an identity
definition with an `implemented_by` implementation proves `check_eq` by `rfl` —
so no specification or proof mentions it, and its compiled form is the in-place
check. It defaults to `assertExclusive` on the whole object, and an object whose
mutable state is a field replaces it: `Counter.check` checks the counter and,
for `record` alone, its log, which is what makes a copy of the log loud. The
check is handed the operation so that it can leave alone what the operation
does not write; an abort must mean that this write is about to copy, not merely
that some part of the object is shared.

## Erasure in `Scidonia/FracPerm`

The permission bookkeeping is specification only. The `Ledger`, the functions
that describe it, and every proof in which it appears live in `Prop` and are
erased. A `ReadTok` is a `Type` and is not erased, but it has no fields and
compiles to a constant scalar (`ctor_0`, the same representation as `Unit`) — no
allocation, no reference counting, and it carries neither the id nor the
fraction. A program runs only through `exec`; the `HSt` accessor is private and
demands an erased capability, so a client cannot choose the ledger a program
starts from. Keep it that way: a primitive's body never computes with the id or
the fraction, and the only state a program threads at run time is one value of
the object's type `σ` (tokens are constant scalars, as above).

An instance is a constant structure of functions, and an object's operations
are the compiled code of its instance and nothing else. The operation types are
`outParam` class parameters rather than fields, because an argument whose
expected type is a projection of the class is not reducible until that
projection's own instance argument is known: instance search does not resolve
the nested goal, so a literal such as the array's `0`, or the pair `(0, 7)`,
could not be given as an operation at all.

The ghost id and the fraction are ordinary `Nat` and `Rat` arguments, and Lean
erases arguments by type, not by use. Literal arguments are dropped by the
compiler's arity reduction (`HSt.acquire._redArg`), and a caller that computes
them is not evaluated at the call; a definition that is generic in them keeps
them as unused `@&` parameters in its own compiled signature, and a use that
arity reduction cannot reach has to compute and box them.
`trace.compiler.ir.result` on a client program is the instrument that shows all
of this.

## The in-place check in the generated C

`HSt.write` runs the object's `check` on the operation and the state before
`update`. For the array that check is `Scidonia.FracPerm.assertExclusiveArray`
and for a general object the default `Scidonia.FracPerm.assertExclusive`; both
are the identity in the logic and, compiled, abort the process when the check
is on and the object is not exclusively owned. The check is on only when
`SCIDONIA_CHECK_INPLACE=1` is in the process environment when the process
starts: the variable is read once, at initialization, into a global the check
branches on, so a write pays one out-of-line call, one load and one branch, and
nothing on the write path reads the environment.

After `nix develop -c lake build`, the generated C of `write`'s lambda is in
`.lake/build/ir/Scidonia/FracPerm/Hoare.c`:

```bash
nix develop -c grep -n -A 14 -- 'HSt_write___redArg___lam__0(lean_object\* v_inst' \
  .lake/build/ir/Scidonia/FracPerm/Hoare.c
```

The lambda projects the instance's `update` and `check`, calls the check with
the write site, the operation and the state, and passes what the check returns
to `update` — so the update in place happens exactly when the check lets it
through, and the state reaches the check owned (the parameter is passed on, not
incremented), which is what keeps a write from copying.

`assertExclusiveArray` and `assertExclusive` are in
`.lake/build/ir/Scidonia/FracPerm/InPlace.c`: the branch on the `inplaceCheck`
global read at initialization, the `lean_is_exclusive_obj` test, and the call to
`reportNotExclusive` that names the site on standard error and exits. The
`Counter`'s own check is in `Counter.c` and does the same for a structure:
`lean_is_exclusive_obj` on the counter, then, for `record` alone,
`lean_ctor_get(s, 1)` and `lean_is_exclusive_obj` on the log — a projection that
takes no reference of its own, so checking the field does not itself share it.
No specification mentions any of it.

Sharing an object is legal — the write copies it, which is not an error — and
the check only turns that copy into a terminated process.

## Layout

| Path | Contents |
| --- | --- |
| `Scidonia.lean` | Root module of the `Scidonia` library |
| `Scidonia/Cyclic/` | Cyclic-proof machinery: graphs, preproofs, ranking progress, terms |
| `Scidonia/FracPerm/` | Fractional-permission objects: `Ledger`, the `FracObject` class and `HSt` in `Hoare`, the `Array` instance, the primitives, `withRead` |
| `Scidonia/FracPerm/InPlace.lean` | The optional run-time check the in-place check calls |
| `Scidonia/FracPerm/Counter.lean` | The worked second object: a count and a log, and the check that covers both |
| `ScidoniaTest/` | Compile-time checks, built as the `ScidoniaTest` library |
| `ScidoniaExamples/` | Worked examples of the fractional-permission interface, built as the `ScidoniaExamples` library |
| `ScidoniaInPlace/` | The `inplace` executable: run-time checks of the in-place update |
| `Main.lean` | Entry point of the `scidonia` executable |
