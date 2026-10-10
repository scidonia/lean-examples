# Scidonia (Lean)

Lean 4 development of the Scidonia proof machinery: the cyclic-proof port under
`Scidonia/Cyclic/` (see `README_LEAN_CYCLIC.md`) and the fractional-permission
object interface under `Scidonia/FracPerm/`, with the structured
`Reader`/`Program` interface beside it under `Scidonia/FracPerm/Structured/`.

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
- `ScidoniaTest/StateVar.lean` checks `Scidonia.FracPerm.StateVar` from outside,
  in the same style. Its behavioural controls are runs of the array witness and
  of the shipped runner; its semantic controls are theorems at the array
  instance (a fork run right branch first computing the sequential denotation's
  value, a read–write–read heap snapshot at concrete operands, the bridge
  equations); and its negative controls are theorems stating that a *specific
  countermodel's* obligation is false — `bad_read_rejected` for
  `observe_detached`, `bad_write_rejected` for `replace_valid`,
  `bad_encode_rejected` for `encodeRead_injective` — paired with the affirmative
  array witness. A `#guard_msgs` pins the countermodel's instance failing to
  elaborate, and `#print axioms` on representative theorems of the theory shows
  which kernel principles they rest on.

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
whose write does not touch the log. Two more children, `structured-unique` and
`structured-closure`, run programs of `Scidonia.FracPerm.Structured` with the
check armed: the array of a structured session is created inside
`runFresh` and never leaves the executor, so those cases are what show that
every `set` of those programs updated in place. The detector those children
show *not* firing is the same `assertExclusiveArray` the existing interface runs
before `update`; the case that shows the check terminating a process is
`checked-abort`, and `shared-copies` is the address control beside it, which
shows the copy itself. See the structured section below for why a structured
case cannot be the one that fires it.

`ScidoniaTest/Structured.lean` checks `Scidonia.FracPerm.Structured` from
outside, in the same library and the same style. Its behavioural checks are
`#eval`s of `runFresh`, because `runFresh` creates the array and so is an `IO`
action: a local `check` throws when a run's value is not the expected one, and
a thrown error fails the elaboration of the module. Its sealing checks are
`#guard_msgs` around commands whose elaboration must fail, with the message
pinned — the private field, the private constructor, the sealed executor's
private array-taking interpreter, and the fact that neither a `Program` nor a
`Reader` is a function that an array can be applied to — each paired with the
affirmative controls: the protocol runs, the eliminators exposing a command tree
and nothing else, and the model's public evaluators running a tree on an array
the client supplies.

## The structured interface

`Scidonia.FracPerm.Structured` is the second interface: a read-only `Reader`, an
exclusive `Program`, and a notional `Reader.parallel`, with the fractions
internal. A program enters a read phase with `Program.readPhase`, runs a tree
of readers there, and writes with `Program.set` only outside one; `runFresh
init p` creates the array from `init` (a size and a fill value), runs the
program, and returns its result. Clients see no fraction, no ghost id, no
ledger and no closing proof, and each of the two computation types carries its
command tree behind a private constructor and a private field, so no client can
build one or project one. The array-taking interpreter (`execP`/`execR` in
`Structured/Executor.lean`) is private to its module, so `runFresh` is the only
runner of the sealed executor and no public function of the sealed executor
accepts an array; the trees the generated eliminators and
`Reader.treeOf`/`Program.treeOf` do expose are recipes — reads, writes, forks
and pure continuations over observations — and carry no state. The model's own
evaluators, `Model.run`/`val`/`pval`, are public and pure: they take the array
from the caller, they are what the theorems are stated about, and they are not
a route to the array a `runFresh` session creates.

`Structured/Model.lean` is the semantics. Threads are running read phases, and
its small-step relation has a step for every interleaving of a fork's branches,
which is what makes `parallel` notional: the shipped executor runs the left
branch and then the right one, and the model proves that every interleaving
computes what the sequential denotation computes (`eval_of_run`,
`complete_run_value`), that a `get` or `size` step hands its continuation
exactly `s[i]?` or `s.size` and leaves the store alone (`step_get`,
`step_size`, `reading_step_store`), that a reader's result is a function of its
observations alone (`replay_trace`), that a well-formed thread's leaf shares sum
to its share and stay positive (`wf_leafSum`, `wf_sharesPositive`), that no
`set` step has a source while a read phase runs and a well-formed reading
configuration leaves the writer no authority (`reading_step_is_read_or_leave`,
`writer_authority_add`), that a `wait` becomes a `run` only when both children
have finished (`wait_step`), and that a `set` preserves the array's size and is
in bounds exactly when it yields `true` (`set_step`, `set_step_size`). Each
theorem's docstring states what it covers; the module note states what the
model assumes — that continuations are arbitrary pure Lean functions of
observations, that the heap is abstracted to the one array, and that in-place
updating is run-time evidence and not a theorem.

The structured interface's fractions are specification too, and more so than
the object interface's: there is no token and no ledger on the run-time path at
all. `WF`, `leafSum` and the share arithmetic live in `Prop` in the model, and
the compiled executor threads one array and the command trees, so a read phase
costs no allocation for permissions — only the continuations the trees already
carry.

The executor's interpreters are the model's recursions with
`assertExclusiveArray` in front of each update (`Executor.execR_eq_val`,
`Executor.execP_eq_pval`, and `runFresh_eq_pval` for the runner), so the
equations that relate the shipped code to the semantics are themselves proved.

`parallel` is notional, and a real concurrent backend would need more than
permissions. The reason is measured on this toolchain: a run-time-built array
captured by a `Task.spawn` closure answers `false` to `isExclusiveUnsafe` after
the task has been joined — it is marked as shared between threads, and
`lean_is_exclusive` refuses it from then on — and the next `set!` returns an
array at a different address, a copy, while the same write on an untasked array
keeps its address. Getting the array back to a single owner is work the
permission discipline does not do. The structured harness cases therefore run
the sequential executor with the check armed; the case that shows that check
terminating a process is the existing `checked-abort` case, and `shared-copies`
is the address control beside it, which shows the copy itself. Neither is a
structured case: a hook that shared a structured session's array would have to
reach the private interpreter, and Lean privacy is per module, so such a hook
would be importable by every client of the library — which is exactly what the
interface's promise, that `runFresh` is the only runner of the sealed executor
and no public route reaches the array a session creates, rules out.

## The generic state variable

`Scidonia/FracPerm/StateVar/` is a second, generic interface beside the
structured one. Where `FracObject` states its two run-time rules in prose
because no specification can check them, `LawfulStateVar` makes the *logical*
part of those rules proof fields, so that the structured model's ownership
theorems hold of every instance that proves them.

* `StateVar/Value.lean` is the logical value language the class's observations
  are encoded in, and `NoRef ℓ v` says an encoded value names no root at `ℓ`.
  `.loc k` is the one constructor that names a root, and `NoRef` descends
  through `some`, `inl`, `inr` and `pair`, so a location hidden beneath a
  compound observation is caught.
* `StateVar/Class.lean` is `LawfulStateVar`: a state type, what it is
  initialized from, its read and write operation types, an encoding of read
  results as `Value`, and `initial_valid`, `replace_valid`,
  `encodeRead_injective` and `observe_detached`. Membership is by proof: no
  `FracObject` instance is automatically lawful, and none of the historical
  instances is claimed as one.
* `StateVar/Surface.lean`, `StateVar/Model.lean` are the generic recipes and
  their small-step model: `RTree`/`PTree`, `run`/`val`, `replay`, `Step`,
  `Eval`, `WF`/`leafSum`, `PStep`/`WFConf`, and `SafeTree`/`safe_result` — M1's
  share conservation, exclusion, join discipline, write preservation, trace
  replay and schedule independence, stated once for every lawful instance.
* `StateVar/Heap.lean` is the single-root logical heap: `At`, `ReadAt`,
  `WriteAt`, the frame and read–write–read snapshot theorems, and M1's fraction
  arithmetic (`ValidShare`, halving, `cannot_add_reader`).
* `StateVar/Array.lean` is the array's witness (`arrayObserve`,
  `arrayReplace`, `encodeArrayRead`, and the instance built from them), the
  translation `liftR`/`liftP` of the structured trees, the denotation bridges
  `bridge_val`/`bridge_pval`, and `runFresh_eq_pval`, which composes M1's own
  `runFresh_eq_pval` with the program bridge.

What the class proves, and what it does not. `observe_detached` refuses a
modeled `.loc ℓ` in a primitive observation of a valid state, and
`encodeRead_injective` rules out a constant encoding; both are statements about
the chosen `Value` encoding, not about Lean's object graph, reference counting
or foreign pointers. An instance that declined to represent a real run-time
pointer as `.loc` would not be caught, and no theorem here certifies that a
compiled write updates in place. The array's in-place evidence therefore stays
where it was: the `inplace` harness (`nix develop -c lake exe inplace`) and the
`structured-unique`/`structured-closure` children that arm the check for the
structured executor. `initial_valid` says a state built from an initializer is
admissible, not that a machine allocation is fresh; `replace_valid` says logical
replacement closes admissible states, not that the old object was destroyed.
Array bounds, size preservation and "`false` exactly when out of bounds" are
array-specific lemmas (`arrayReplace_size`, `arrayReplace_bounds`), not class
laws, because a different state variable replaces unconditionally.

The generic model is recipes and proofs, not a second backend. It adds no
runner: the structured interface's sealed `Reader`/`Program`/`runFresh` and its
private interpreters are unchanged, the new trees are pure data with no array,
share or ledger in them, and `liftR`/`liftP` reveal nothing beyond the trees
`Reader.treeOf`/`Program.treeOf` already expose. Its limits are M1's: a
continuation is an arbitrary pure Lean function of observations, so nothing
implies that all continuations terminate; failure is not modelled; a `fork`'s
branches are run in either order by the semantics while the shipped executor
runs left and then right, and no theorem claims real concurrent task execution.
The heap is a simulation of the model's single state, with correspondence
theorems (`readAt_step_observe`, `pstep_write_corresponds`) rather than claims
about machine memory: writing produces a new heap value, and no address is
preserved.

`replay` is the one noncomputable definition in the theory: comparing two
operations is a logical side condition, so it uses `Classical.propDecidable` and
is model-only. `ScidoniaTest/StateVar.lean` prints the axioms of representative
theorems of the theory; they are the standard kernel principles only.

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

The structured executor's generated C is what shows its array reaching `set`
with one reference. `execP` compiles to a loop that carries the array in a
local, and its `set` case passes that local to `assertExclusiveArrayImpl`
with no `lean_inc` in front of it, then hands `lean_array_set`'s result back to
the loop; its `phase` case passes the same local to `execR`, whose array
parameter is `@&` and is therefore borrowed rather than taken, so a read phase
costs no second reference. `runFresh`'s `Array.replicate` is a `lean_mk_array`
at run time and is handed to `execP` owned. The relevant function in the
generated C is:

```bash
nix develop -c grep -n "assertExclusiveArrayImpl" \
  .lake/build/ir/Scidonia/FracPerm/Structured/Executor.c
```

The call site is the one the `structured-unique` and `structured-closure`
children exercise: they exit zero with the check armed, having printed
`check-enabled=true`, so the check was in the write path and had nothing to
report.

## Slides

`Slides/` holds a reveal.js deck on the fractional-permission work, built
with the generator of the sibling checkout `../vericoding-tutorial`
(`scripts/build_deck.py`, Python standard library only). It runs under this
repository's dev shell through `lake env`, so every Lean panel is compiled
against this repository's library on its pinned toolchain, and a panel Lean
rejects fails the build. Build the libraries first; the deck imports
`ScidoniaTest`:

```sh
nix develop -c lake build ScidoniaTest
nix develop -c lake env python3 ../vericoding-tutorial/scripts/build_deck.py \
  --prose Slides/permissions.md \
  --example Slides/RoundTrip.lean \
  --prose Slides/runtime.md \
  --title "Fractional permissions in Lean 4" \
  --subtitle "Erased ghost state, Hoare monads and in-place update" \
  --output Slides/fracperm.html
```

The prose format and the panel rules are those of the generator, documented in
`../vericoding-tutorial/AGENTS.md`; a `@path` quotation resolves in that
repository, not this one, so quote code here as a compiled panel. The built
`Slides/*.html` is not committed.

## Layout

| Path | Contents |
| --- | --- |
| `Scidonia.lean` | Root module of the `Scidonia` library |
| `Scidonia/Cyclic/` | Cyclic-proof machinery: graphs, preproofs, ranking progress, terms |
| `Scidonia/FracPerm/` | Fractional-permission objects: `Ledger`, the `FracObject` class and `HSt` in `Hoare`, the `Array` instance, the primitives, `withRead` |
| `Scidonia/FracPerm/Structured/Surface.lean` | The structured interface: `Reader`, `Program`, their command trees, `Init` |
| `Scidonia/FracPerm/Structured/Executor.lean` | The sequential executor: the private interpreters and the sealed runner, `runFresh` |
| `Scidonia/FracPerm/Structured/Model.lean` | The small-step model, the shares, and the ownership theorems |
| `Scidonia/FracPerm/StateVar/Value.lean` | The logical value language and `NoRef` |
| `Scidonia/FracPerm/StateVar/Class.lean` | The `LawfulStateVar` class and its law scopes |
| `Scidonia/FracPerm/StateVar/Surface.lean` | The generic recipes: `RTree`, `PTree` and their binds |
| `Scidonia/FracPerm/StateVar/Model.lean` | The generic small-step model: `run`/`replay`, `Step`, `Eval`, shares, `PStep`, `SafeTree` |
| `Scidonia/FracPerm/StateVar/Heap.lean` | The single-root heap: `At`, `ReadAt`, `WriteAt`, frames, snapshots, shares |
| `Scidonia/FracPerm/StateVar/Array.lean` | The array witness, `liftR`/`liftP`, the bridges, and the `runFresh` equation |
| `Scidonia/FracPerm/InPlace.lean` | The optional run-time check the in-place check calls |
| `Scidonia/FracPerm/Counter.lean` | The worked second object: a count and a log, and the check that covers both |
| `ScidoniaTest/` | Compile-time checks, built as the `ScidoniaTest` library |
| `ScidoniaTest/Structured.lean` | The structured interface's protocol and sealing checks |
| `ScidoniaTest/StateVar.lean` | The generic state variable's witness, model, bridge, and negative-law checks |
| `ScidoniaExamples/` | Worked examples of the fractional-permission interface, built as the `ScidoniaExamples` library |
| `ScidoniaExamples/Structured.lean` | Worked examples of the structured interface |
| `ScidoniaInPlace/` | The `inplace` executable: run-time checks of the in-place update |
| `Slides/` | The slide deck's sources: two prose series and a stepped proof |
| `Main.lean` | Entry point of the `scidonia` executable |
