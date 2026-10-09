# Scidonia (Lean)

Lean 4 development of the Scidonia proof machinery: the cyclic-proof port under
`Scidonia/Cyclic/` (see `README_LEAN_CYCLIC.md`) and the fractional-permission
array interface under `Scidonia/FracPerm/`.

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
  a proposition about `HArr.pre` or about the closing condition of `HArr.exec`,
  not merely a tactic that is expected to fail.
- `ScidoniaTest.lean` is the root module of the check library. Lake needs it
  because a library's root is the module named after the library, and the file
  must import the modules that carry the checks.

The in-place check of `Scidonia.FracPerm` is checked by running rather than by
elaboration: `nix develop -c lake exe inplace` runs `ScidoniaInPlace/Main.lean`,
which observes the address and the reference count of the array the interface
threads and relaunches itself with `SCIDONIA_CHECK_INPLACE=1` to check that a
write which would copy terminates the process. The file documents its cases.

## Erasure in `Scidonia/FracPerm`

The permission bookkeeping is specification only. The `Ledger`, the functions
that describe it, and every proof in which it appears live in `Prop` and are
erased. A `ReadTok` is a `Type` and is not erased, but it has no fields and
compiles to a constant scalar (`ctor_0`, the same representation as `Unit`) — no
allocation, no reference counting, and it carries neither the id nor the
fraction. A program runs only through `exec`; the `HArr` accessor is private and
demands an erased capability, so a client cannot choose the ledger a program
starts from. Keep it that way: a primitive's body never computes with the id or
the fraction, and the only state a program threads at run time is the
`Array α` (tokens are constant scalars, as above).

The ghost id and the fraction are ordinary `Nat` and `Rat` arguments, and Lean
erases arguments by type, not by use. Literal arguments are dropped by the
compiler's arity reduction (`HArr.acquire._redArg`), and a caller that computes
them is not evaluated at the call; a definition that is generic in them keeps
them as unused `@&` parameters in its own compiled signature, and a use that
arity reduction cannot reach has to compute and box them.
`trace.compiler.ir.result` on a client program is the instrument that shows all
of this.

## The in-place check in the generated C

`HArr.write` guards its array with `Scidonia.FracPerm.assertExclusive`, which is
the identity in the logic and, compiled, aborts the process when the check is
on and the array is not exclusively owned. The check is on only when
`SCIDONIA_CHECK_INPLACE=1` is in the process environment when the process
starts: the variable is read once, at initialization, into a global the check
branches on, so a write pays one out-of-line call, one load and one branch, and
nothing on the write path reads the environment.

After `nix develop -c lake build`, the generated C of `write`'s lambda is in
`.lake/build/ir/Scidonia/FracPerm/HoareArray.c`:

```bash
nix develop -c grep -n -A 14 -- 'write___redArg___lam__0(lean_object\* v_i' \
  .lake/build/ir/Scidonia/FracPerm/HoareArray.c
```

The lambda calls `lp_Scidonia_Scidonia_FracPerm_assertExclusiveImpl___redArg`
with the write site and the array, and passes what it returns to
`lean_array_set` — so the update in place happens exactly when the check lets it
through. `assertExclusiveImpl` itself is in
`.lake/build/ir/Scidonia/FracPerm/InPlace.c`: the branch on the `inplaceCheck`
global read at initialization, the `lean_is_exclusive_obj` test, and the call to
`reportNotExclusive` that names the site and the array's size on standard error
and exits. No specification mentions any of it.

Sharing an array is legal — the write copies it, which is not an error — and
the check only turns that copy into a terminated process.

## Layout

| Path | Contents |
| --- | --- |
| `Scidonia.lean` | Root module of the `Scidonia` library |
| `Scidonia/Cyclic/` | Cyclic-proof machinery: graphs, preproofs, ranking progress, terms |
| `Scidonia/FracPerm/` | Fractional-permission array: `Ledger`, `HArr`, the primitives |
| `Scidonia/FracPerm/InPlace.lean` | The optional run-time check `write` guards its array with |
| `ScidoniaTest/` | Compile-time checks, built as the `ScidoniaTest` library |
| `ScidoniaExamples/` | Worked examples of the fractional-permission interface, built as the `ScidoniaExamples` library |
| `ScidoniaInPlace/` | The `inplace` executable: run-time checks of the in-place update |
| `Main.lean` | Entry point of the `scidonia` executable |
