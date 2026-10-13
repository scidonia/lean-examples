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
- `ScidoniaTest/Slot.lean` checks the description-indexed slot from outside, in
  the same style: the two inverse laws at concrete slots and over all slots
  (including a payload of two hundred binary digits), the class's operations on
  slots, the read–write–read heap snapshot at `full 7` → `full 9` — both through
  the generic `snapshot_after_write` and through the slot-specific statement —
  the `empty → full n → empty` shape change on one root cell, and the
  no-reference detector's positive and negative pair. Its `#print axioms` shows
  the new theorems rest on the standard kernel principles only.
- `ScidoniaTest/Universe.lean` checks the description universe and the transport
  from outside, in the same style: `encodeEl` at a unit, a natural, each summand
  of a sum and all four summands of a nested sum; the single instance's
  operations at those shapes and the injectivity and no-reference laws
  quantified over *every* description; the generic snapshot, frame and validity
  theorems applied at an arbitrary description; and a second, independent
  transport for `Bool` at `sum unit unit`, a description the slot does not use,
  so the transport is not exercised only by its one client. Its `#print axioms`
  shows the new theorems rest on the standard kernel principles only.
- `ScidoniaTest/Model5.lean` checks `Scidonia.FracPerm.StateVar.Layout5` from
  outside, in the same style. Its behavioural checks are `#guard`s of `read?` at
  a leaf of an array of structs, at a nested struct, at a root leaf and at an
  out-of-bounds index, and of the values a path write leaves; its semantic checks
  are the zipper's round trip, the path replacement, the failure equation, the
  read–write–read snapshot at `7 → 9` (the two readings are different, so the
  first conjunct cannot stand in for the criterion) and the frame at a sibling
  field and at another array index, each stated both universally and at concrete
  paths. Its privacy pins are `#guard_msgs` rejections of `«open»`, `plug`,
  `Context`, `takeOut` and `plugAt`, beside an affirmative `#check` of `read?`,
  which is how the raw-focus boundary is observed from outside the module. Its
  negative checks are a `#guard_msgs` rejection of a whole-array read
  path, the class's own detector, and a **countermodel instance**: a
  `LawfulStateVar (Array UInt64)` whose read returns the array itself, with a
  constructor-faithful, injective, no-reference array encoder, so all four class
  laws hold and the class accepts it. That instance is what Model 5's leaf-only
  read path closes — its read returns an observation of the closed universe and
  a path cannot address a whole array. Its `#print axioms` shows the new
  theorems rest on the standard kernel principles only. The kernel cannot reduce
  `read?` on an `Array` literal, because `Array`'s primitives are opaque to it,
  so the concrete readings are established by `#guard` (which evaluates the
  compiled definitions) and the theorems about them take the read as an
  assumption.
- `ScidoniaTest/Sealed.lean` checks `Scidonia.FracPerm.StateVar.SealedStateVar`
  from outside. Its behavioural checks are `#guard`s of `SealedStateVar.read?`
  and `SealedStateVar.setLeaf` on the two shipped instances — a leaf of an array
  of structs, a leaf of a nested array, and an out-of-bounds index — and its
  semantic checks are the four theorems at the concrete instance: detachment, the
  read after a successful write, the `7 → 9` snapshot, the frame at a sibling
  field, and the failure equation. Its structural checks pin what the class
  cannot do: a `#guard_msgs` rejection of an instance that adds an `observe`, one
  that adds an `encodeRead`, and one whose `rep` names a layout the type is not,
  plus the observation that `SealedStateVar.observe` and
  `SealedStateVar.encodeRead` are not names a client can write — beside
  affirmative `#check`s of the class's fields and of the public read and write.
  Its comparison with the old class cites the countermodel: `LawfulStateVar`
  admits an instance whose read is the mutable array, and the same instance shape
  offered to the sealed class is rejected, which is what makes the sealed
  guarantee structural. Its `#print axioms` shows the new theorems rest on the
  standard kernel principles only.
- `ScidoniaTest/Count.lean` checks `Scidonia.FracPerm.StateVar.RefCount` from
  outside. Its controls are counts that tell the module's two tests apart: the
  exclusive count itself — the affirmative control for the hypothesis of
  `not_exclusive_incRefN_one`, which would otherwise say nothing about any count
  — the count a single-threaded overflow freezes at (`isUnshared` and not
  `IsExclusive`), a persistent count, and the thread-shared count that sharing
  leaves. The hazard pair `1 → 2 → 1` is the release's step as a theorem and the
  increment's step as a `#guard`, because the kernel cannot reduce `incRefN`,
  whose guard is a `USize` comparison — the limit the vendored file's own
  concrete examples hit, where they are proved by native evaluation. Its
  `#print axioms` groups the theorems in three. The vendored block's seventeen
  public theorems are all printed and read: thirteen carry a generated
  certificate axiom beside `propext`, `Classical.choice` and `Quot.sound`,
  because `bv_decide` decides by native evaluation and asserts the result as an
  axiom, and four print none: `LEAN_RC_STUCK_ST_eq`, `incRefHugeMt_id`,
  `decRef_spec` and `frozen_shared_count_stays_shared`, of which only the first
  invokes `bv_decide` at all — the other three are `grind` and `omega` proofs.
  The facts derived from a vendored theorem are printed with their
  source named: `run_never_exclusive` inherits the axioms of the vendored
  `run_never_frees`, and `stuckSt_is_unshared_not_exclusive`, stated through the
  vendored `LEAN_RC_STUCK_ST_eq`, inherits the standard principles only. This
  repository's own facts are asserted rather than printed — each `#guard_msgs`
  pins the list `#print axioms` emits, so any other axiom fails the build — and
  the file's own proofs use `grind`, `simp` and `decide`, which add none.
- `ScidoniaTest/Footprint.lean` checks `Scidonia.FracPerm.StateVar.Footprint`
  from outside, in the same style. Its behavioural checks are `#guard`s of
  evaluated counts on small presentations — a chain of cells read from one
  handle, a store whose two slots name one cell, a store plus a second handle, a
  store that names no cell, and one cell's slots cut — each with a control
  beside it: a false equation of the same shape whose message is pinned, so a
  guard is shown to fire rather than to pass whatever it is given. Its negative
  controls are theorems about specific presentations — the aliased cell and the
  second-handle chain are not exclusive — and each stands beside an affirmative
  control at the *same* presentation, the root the one handle names, so the
  negative is about the reference and not about the presentation being rejected
  everywhere. Its affirmative structural controls apply the single-handle, pair
  and one-cell-write theorems at those presentations and read both sides of the
  discipline theorem off one call. Its composition checks apply the
  detached-issues theorem at a store and a detached value list, and its
  countermodel gives the same shape a value that names the root. `#print axioms`
  is asserted for representative theorems, and the runtime link's reverse
  direction is pinned by the message `#check` emits, so a statement under that
  name that changes fails the build. The runtime link itself is never
  constructed: the checks take it as a hypothesis.
- `ScidoniaTest/RCHeap.lean` checks the counted heap from outside: evaluated
  counts and both branches' locations on small heaps, each with a pinned failing
  control beside it; the duplicate-key heap failing the well-formedness invariant
  and a release leaving no zero-count or orphaned cell, each with an affirmative
  control at the same heap; the bridge, both location statements and both
  `Counted` preservation theorems applied at those heaps; and asserted `#print
  axioms` lists.
- `ScidoniaTest/IRShape.lean` is the one check made of the compiler's own output
  rather than of the library's terms. It reaches the environment during
  elaboration and reads the post-reference-counting IR of the write paths with
  `IR.findEnvDecl`, then requires the shape the measurement records — the
  take-out's `Array.getInternal` and placeholder `Array.set`, the array check,
  the focus check, the recursion and the write, with every operand relation bound
  to one occurrence selection on one executing path — and requires the borrowed
  `Array.getInternalBorrowed` absent there, with a same-detector control finding
  it where it exists (the bounds walk, the structured reader). A failed
  requirement fails the elaboration, so `lake build ScidoniaTest` is the gate; a
  detector weakened to match nothing fails the build rather than passing quietly.
- `ScidoniaTest/Run.lean` checks the run model from outside: evaluated steps and
  path resolutions on short heaps and programs, each with a pinned control beside
  it — including a step a check turns away, which does not run; the countermodel
  and its affirmative counterpart at the *same* heap and path, the pair's handle
  held giving a count of two and a copy and the same update keeping its location
  once it is dropped; the per-step and per-run theorems applied at concrete
  sequences; and asserted `#print axioms` lists.
- `ScidoniaTest/RC.lean` checks the calculus and the lowering from outside:
  evaluated steps and evaluated translations on small terms with a pinned control
  beside every guard, including the capture pair — a closed term reading its
  definition-time value beside an open term that demonstrably captures — the
  non-value-argument case, a term needing a `dup` and one needing a `drop`, and
  asserted `#print axioms` lists.
- `ScidoniaTest/Target.lean` checks the target runtime from outside: evaluated runs
  on small counted heaps with a control beside each, the owned store keeping its
  location beside the shared store copying at the *same* heap and term, each of the
  target's evaluation contexts exercised with a negative control, the refusal of the
  mis-tagged multiplicity pair, and asserted `#print axioms` lists.

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

The path writes of `Scidonia.FracPerm.StateVar.Layout5` are checked the same
way, and they are the cases that put the take-out on a real
`Array (UInt64 × UInt64)`: `layout5-unique`, `layout5-right`, `layout5-last` and
`layout5-out-of-bounds` check the values a path write leaves and that the array's
buffer and the sampled sibling struct each case names keep their addresses;
`layout5-shared-copies` is the control that shows a live second reference to the
array makes the write copy; `layout5-checked-unique` is the same unique write in
a child with the check armed, which must exit zero because the take-out's array
and the element it extracted are both exclusively owned; and
`layout5-checked-shared` is the aliased write with the check armed, which must
end the process naming the `Layout5` site. The nested cases put the measurement
on the focused element: `layout5-nest` asserts the focused inner array's own
address is unchanged (and `layout5-checked-nest` exits zero),
`layout5-nest-aliased` holds a live reference to that inner array and asserts its
address changes, and `layout5-checked-nest-shared` is that write with the check
armed, which must end the process naming the element's site. The struct at the
written index is a `Prod` and the update returns the state alone, so the
compiler's reset/reuse pass rewrites that cell in place: `layout5-unique` asserts
it keeps its address and `layout5-shared-copies` asserts it changes when a live
second reference reaches it; see the Model 5 section below for what that does
and does not show. The sealed write is checked the same way:
`sealed-unique` drives `SealedStateVar.setLeaf` on the shipped
`Array (UInt64 × UInt64)` instance and asserts the array's buffer and the struct
at the written index are unchanged, and `sealed-checked-unique` is that write in
a child with the check armed, which must exit zero.

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
* `StateVar/Description.lean` is the description universe a description-indexed
  state variable is written against: `Desc` (`unit`, `nat`, `sum`), the type
  `El d` a description denotes, and `slotDesc`, the description of a slot (a
  unit summed with a natural). `El` is an `abbrev`, so `El slotDesc` is
  definitionally `Sum Unit Nat` for a client.
* `StateVar/Universe.lean` is the universe as one lawful state variable, and the
  transport that carries it to any isomorphic type. `encodeEl` encodes an
  element of *any* description as a `Value`, and `encodeEl_injective` and
  `encodeEl_noRef` are each proved *once*, by a structural induction on `Desc`
  with one case per constructor, rather than once per description. The wrapper
  `Described d` indexes typeclass inference by the description (two descriptions
  can denote definitionally equal Lean types), so the single instance
  `describedStateVar d : LawfulStateVar (Described d) (El d) Unit (El d)` serves
  every description; the generic model's theorems are then applied at it for an
  arbitrary `d` (`universe_read_after_replace`, `universe_read_detached`,
  `universe_read_at_detached`, `universe_write_at_valid`,
  `universe_write_at_frame`, `universe_snapshot_after_write`). `transport d τ
  toEl ofEl …` is the other half: any type with an isomorphism to `El d` gets a
  lawful instance whose operations are the universe instance's conjugated by the
  isomorphism, with each law the universe's after an inverse law cancels the
  conjugation.
* `StateVar/Slot.lean` is the worked description-indexed state variable: the
  genuine `inductive Slot` (empty, or a natural payload), `encode`/`decode` and
  both inverse laws `decode_encode`/`encode_decode`, and `lifted_iff`. Its
  instance `slotStateVar` is `transport slotDesc Slot encode decode …`: every
  operation is the universe instance's conjugated by `encode`/`decode`, and
  every law field is the universe instance's law after an inverse law cancels
  the conjugation — no fresh proof, and nothing specific to `slotDesc`. Its
  theorems are `slot_observe_eq`/`slot_replace_eq`/`slotEncodeRead_eq`,
  `slot_read_after_replace`, the read–write–read snapshot
  `slot_snapshot_full7_full9` (the old `full 7` still the value of the pre-write
  heap, the post-write cell holding `full 9`), the shape change
  `slot_shape_change` (`empty → full n → empty` on one root cell), and the
  arbitrary-payload facts `slot_full_round_trip` and
  `slot_read_after_replace_full`.

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

The slot is the second witness, and it is a *logical* one in the same sense: its
`replace` takes effect unconditionally (`(new, true)`), since a single root cell
has no bounds to fail, and `slot_snapshot_full7_full9`/`slot_shape_change`
replace a root cell in the model's `Heap Slot` (`Loc → Option Slot`). It is not
proved from nothing: the universe gives one lawful instance for every
description, and the slot's is a transport of it at `slotDesc`. A write there
yields a new heap value and destroys nothing — the old value is still what the
pre-write heap holds — so this is neither physical fixed-node mutation nor an
address-preservation claim, and no `IO.Ref`, C or foreign backend is involved.
`ScidoniaTest/Slot.lean` and `ScidoniaTest/Universe.lean` are where a client's
view of it is checked.

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

## Model 5: paths, detached observations, and take-out writes

`Scidonia/FracPerm/StateVar/Layout5.lean` is the fifth model. Where the class's
state is one description-indexed element, a layout has *structure*: `ObsDesc` is
the closed observation universe (unit, natural, word, boolean, sum, option,
pair) — no array, struct or reference appears in it — `Layout` is a leaf of that
universe, a binary `struct` (so arbitrarily many fields by nesting) or an `arr`,
and `State` is the type a layout denotes. A `Path` is an address whose `index`
step is dynamic: whether it addresses anything is a property of a particular
state. An `ObsPath` is a path together with the leaf description its end must
have, and that proof field is what makes a whole-array read *unwritable*:
`At p = .leaf o` has no solution at an `.arr` or `.struct` end, so
`array_root_not_observable` and the `#guard_msgs` rejection in the check library
are the same fact seen from two sides.

A read ends only at a leaf of the closed universe. `read?` returns
`Option Value` — the library's `encodeObs` of the observation the path ended at,
or `none` for an index that addresses nothing — and its traversal (`leafAt?`) is
private, so the raw focus is obtained and encoded in one step and no function
returns a state. `encodeObs_injective` and `encodeObs_noRef` are proved once, by
structural induction over the universe, and `read_detached` is their
consequence: a successful read names no `.loc`, so it cannot hand back a
mutable part of the state.

The zipper is the write's private *specification*. `Context d p` is the one-hole
context of a path, `open` takes a state apart into a context and a focus (or
reports the original state, for an index that addresses nothing at any depth),
and `plug` puts a focus back; all of them are private, so a client cannot obtain
a raw focus. `setLeaf` is a structurally recursive update of its own — it asks
`inBounds` whether the path addresses anything, then rebuilds each struct cell
from its updated component and takes the array case out, checks it, recurses and
puts it back — and it is proved equal to the zipper's path replacement by
`setAt_spec`, so every theorem stated through `setLeaf` holds of the
specification. The update threads the new focus through the recursion as the
focus of the path rather than as a function of the old state, so a write
allocates no closure; the cast from the observation to the path's state type
happens once, in `setLeaf`, and erases. `open_plug` is the zipper's round
trip, `plug_update` says a successful write is the path replacement, `open_failed`
says a failed `open` reports the state it was given, and `setLeaf_failed` says a
failed write leaves the state alone. `snapshot_after_setLeaf` binds the earlier
read to the *old* state and the read after the write to the write's own operand,
and `read_frame` says a write at a path disjoint from a read path — `Disjoint`
excludes the equal paths and every ancestor/descendant pair, not merely paths
whose final fields differ — does not change what that read returns.

The array case is a **take-out** write. `takeOut` is an owned `Array.swapAt`
exchange that leaves the layout's placeholder in the selected slot and hands the
element back, so the array keeps its size and every other slot; `plugAt` is the
inverse exchange that puts a focus back. Both are private, like the zipper: they
hand back the raw element an update below the slot works on, so a client reaches
them only through `read?` and `setLeaf`. The pair `takeOut` returns is
destructured before anything is checked or recursed into, and the path below it
is taken apart on the extracted element itself. The array's exclusivity is not
the element's — the take-out replaces one slot, and a caller that built an
aliased array can leave another slot pointing at the same object — which is why
the extracted element is checked on its own. If the path below cannot be opened,
the state the inner `open` reported is put straight back — the element it was
given — so the failure reports the original array.

Two `assertExclusive` checks guard the mutation, and both are the difference
between an update in place and a copy: the check on the *array*, before the
take-out, because a shared array is copied whole; and the check on the
*extracted focus*, before the update below it runs, because a shared element — a
spare slot, or an alias a caller kept — is what a write inside it would copy.
Two instruments report different things and are not interchangeable: the
generated C of `setAt`'s array case — the recursion `setLeaf` executes, not
`open`, which is the zipper specification — shows the ownership and the order —
the pair the take-out returned converted to its two locals and released, the
focus check after it, the recursion on the check's result, and the put-back —
while `ScidoniaInPlace`'s `addressIO` observations, with the assertions the
harness puts on them, are what establishes that an address is unchanged or
changed.

`describedLayoutStateVar d` is the adapter: a layout state is a lawful state
variable whose reads are `read?`, whose writes are `setLeaf`, and whose encoding
is `encodeObs`. It is a value of the existing class built from library
definitions — an author supplies neither the encoder nor the read operation — so
the generic model's and the heap's theorems apply at it
(`describedLayout_read_after_replace`, `describedLayout_primitive_detached`,
`describedLayout_read_at_detached`, `describedLayout_write_at_valid`,
`describedLayout_write_at_frame`) without a new proof.

What Model 5 does not claim. The raw-focus routes are private: `Context`,
`open`, `plug`, the laws about them, and the take-out (`takeOut`, `takeOutAt`,
`plugAt` and their lemmas) are not exported, because each hands back either a
focus or the raw element an update below a slot works on, so a client that could
call one could keep a mutable node — an inner array — past a leaf. The read
guarantee is about the public `read?`/`setLeaf` surface: `read?` never returns a
state or a subtree, and `ScidoniaTest/Model5.lean` pins the privacy from outside
with `#guard_msgs` around a use of `«open»`, of `plug`, of `Context`, of
`takeOut` and of `plugAt`, each beside an affirmative `#check` of `read?`.
Whether a compiled write updates in place is run-time evidence from
`ScidoniaInPlace`, not a theorem: the harness's `layout5-unique`,
`layout5-right`, `layout5-last` and `layout5-out-of-bounds` cases check the
values and the addresses of the unique array, and `layout5-shared-copies` is the
control that shows a live second reference to the array makes the write copy.
`layout5-checked-unique` runs with `SCIDONIA_CHECK_INPLACE=1` and exits zero, and
`layout5-checked-shared` shows the same write on a shared array terminating the
process with the array's site on standard error. The extracted element is
checked too, before the update below it runs, because a write inside it is what a
shared element would copy: `layout5-nest` writes a leaf of an inner array and
asserts the inner array's own address is unchanged, with `layout5-checked-nest`
exiting zero, while `layout5-nest-aliased` holds a live reference to that inner
array and asserts its address changes (the outer array's does not) and
`layout5-checked-nest-shared` is that write with the check armed, which
terminates naming the element's site. The struct at the written slot is a `Prod`
and the update returns the state alone, so the compiler's reset/reuse pass
rewrites that cell in place: `layout5-unique` asserts it keeps its address, and
`layout5-shared-copies` asserts it changes when a live second reference reaches
it. Array bounds, size preservation and the take-out round trip are
instance-specific private lemmas (`takeOut_fst`, `takeOut_bound_of_eq`,
`plugAt_size`, `plugAt_takeOut`), not class laws. The old class is unchanged: it
still accepts an instance whose encoding is honest by its own lights and whose
read names the state (`ScidoniaTest/Model5.lean`'s countermodel shows exactly
that), so the historical `FracObject` and `LawfulStateVar` obligations remain
prose or per-instance proofs and are not automatically enforced for historical
instances.

## Sealed state variables

`Scidonia/FracPerm/StateVar/Sealed.lean` is the same guarantee as a class rather
than a wrapper. `SealedStateVar σ` asks an instance for exactly two things: the
layout `σ` is, and `rep : σ = State layout`. It has no field for a read, a write
or an encoding, so an instance cannot supply one, and the library defines the
operations once from `rep`:

```lean
SealedStateVar.read? (p : ObsPath layout) : σ → Option Value
SealedStateVar.setLeaf (p : ObsPath layout) (x : ObsEl p.obs) : σ → σ × Bool
```

Both are the layout's operation after the cast in `rep`: `read?` is `Layout5.read?`
at the transported state, and `setLeaf` is `Layout5.setLeaf` with the state cast
in and the state it returns cast out. `sealedLawful [SealedStateVar σ]` is the
derived `LawfulStateVar σ σ (ObsPath _) (LayoutWrite _)`: Model 5's adapter
transported along `rep`, so its four laws are the adapter's rather than per
instance, and its read result (`Option (ObsEl p.obs)`) and its encoding (the
library's `encodeObs` of the observation) are fixed by `rfl` — an instance
supplies neither. The theorems restate Model 5's for every sealed instance:
`sealedRead_detached` (a read result names no `.loc`), `sealedRead_after_setLeaf`
and `sealedSnapshot` (the read after a successful write is the written
observation, while an earlier read keeps the old state's value),
`sealedRead_frame` (a write at a disjoint path changes no other read), and
`sealedSetLeaf_failed` (a failing write leaves the state alone).

What is checked is what is observed. `ScidoniaTest/Sealed.lean` pins the absence
of the fields from outside — an instance that tries to add an `observe` or an
`encodeRead` is rejected by elaboration, `rep` cannot name a layout the type is
not, and `SealedStateVar.observe` is not a name a client can even write — beside
the affirmative `#check`s and the positive reads and writes on both shipped
instances (`Array (UInt64 × UInt64)` and `Array (Array UInt64)`), and beside the
countermodel comparison: `LawfulStateVar` still admits the leaky array instance
of `ScidoniaTest/Model5.lean`, and `SealedStateVar` has no field to put that read
in. Whether the write is in place is the run-time evidence of `ScidoniaInPlace`:
`sealed-unique` drives `SealedStateVar.setLeaf` on the array-of-structs instance
and asserts the array's buffer and the struct cell at the written index both
keep their addresses, and `sealed-checked-unique` is the same write with
`SCIDONIA_CHECK_INPLACE=1`, exiting zero. The cast costs nothing: the generated C
of the sealed write calls `Layout5.setLeaf` with the state unchanged — no
boxing, no conversion, no closure — and reuses the pair it returns, because the
instance's `rep` is `rfl` and the two casts erase.

Scope limit: a *user-declared* `structure` cannot be sealed. `rep : σ = State
layout` must be an equality, and for a structure of one's own the only relation
to a layout's state type is an isomorphism, not an equality. An isomorphism-based
variant would have to convert between the two representations on writes; whether
that costs a copy has not been implemented or measured here. Arrays, nested
arrays, pairs and the observation universe's leaves are usable, because `State`
denotes them definitionally.

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

## The reference count, as a write sees it

`Scidonia/FracPerm/StateVar/RefCount.lean` is the counter-level vocabulary of the
write path: what a Lean reference count is, what an increment and a drop do to
it, and the predicate a write tests before it may store in place. It is vendored
— unchanged, and with the declarations keeping their own names inside the
module's namespace — from `leanprover/lean4`'s own machine-checked model of
`lean_inc_ref_n` and `lean_dec_ref`, `tests/elab/rc_model.lean` at the tag
`v4.35.0-rc3` (Apache 2.0, the Lean 4 licence): the thresholds
(`LEAN_RC_STICKY`, `LEAN_RC_STICKY_DROP`, `LEAN_RC_INC_MAX`, `LEAN_RC_STUCK_ST`),
the kinds a count falls into (`isSt`, `isMt`, `isPersistent`, `isStuck`,
`isStuckSt`, `isUnshared`, `isNeverFreed`), `refCount`, the adjustments
`incRefN`, `decRef` and `markMtRc`, and the theorems that say what they mean
(`incRefN_spec`, `decRef_spec`, `markMtRc_spec`, `never_freed_is_absorbing`,
`run_spec`, `run_never_frees`). Those declarations are the Lean FRO's, not this
repository's; the module header says so, and this repository's own declarations
begin after the vendored block.

Two predicates are what a write reads:

```lean
def IsExclusive (rc : Int32) : Prop := isSt rc ∧ rc = 1   -- lean_is_exclusive
def IsUnshared (rc : Int32) : Prop := isUnshared rc       -- is_unshared
```

`IsUnshared` is strictly weaker, and the two are not interchangeable: the
runtime's `is_unshared` is `rc > 0 || rc ≤ LEAN_RC_STUCK_ST`, so a count that
overflowed while single-threaded reads as unshared while standing for references
it can no longer track — it passes `IsUnshared` and fails `IsExclusive`, and a
write that tested only the former would drop the other references.
`ScidoniaTest/Count.lean` exhibits that count. The facts beside the predicates
are what the discipline rests on: an extra reference costs the in-place update
(`not_exclusive_incRefN_one`), dropping it restores it (`decRef_two`), a
thread-shared count is never exclusive (`markMtRc_not_exclusive` — the
`Task.spawn` measurement, read off the model), a never-freed count never becomes
exclusive however the adjustments run (`not_exclusive_of_neverFreed`,
`run_never_exclusive`), and the take-out's arithmetic leaves the caller's value
one reference (`takeOut_refCount_eq_one`).

That last one is an **assumption**, and the module labels it as one: taking a
value out of a store cell is a run-time operation on the object, not a counter
operation, so the store does not appear in the module at all — the two
counter-level effects of its take-out are the theorem's hypotheses, and which
cell a store holds and what its primitive does are the caller's obligation.
Non-escape over the command tree and the shape of the emitted `Lean.IR` are not
in this module either.

What a proof rests on is printed rather than assumed, and the trusted surface is
kept where the vendoring forces it:

- `bv_decide` and `mvcgen` are used **only inside the vendored block**, which is
  upstream's text. `mvcgen` is that block's tactic for the `Id.run` loops: it
  generates verification conditions and is not itself a source of an axiom —
  `incRefHugeMt_id` is `mvcgen` then `grind` and carries the standard principles
  alone. `bv_decide` is the one that can add a generated certificate axiom
  (`<theorem>._native.bv_decide.ax_*`) beside `propext`, `Classical.choice` and
  `Quot.sound`, by evaluating its certificate and asserting the result. Thirteen
  of the block's seventeen public theorems carry at least one such axiom; four
  print none — `LEAN_RC_STUCK_ST_eq`, `incRefHugeMt_id`, `decRef_spec` and
  `frozen_shared_count_stays_shared` — and of those only `LEAN_RC_STUCK_ST_eq`
  invokes `bv_decide` at all, its goal having been closed before the certificate
  step; the other three are `grind` and `omega` proofs, which add no axiom.
  Those axioms, where they are there, are not
  this repository's to remove, and the module leaves the vendored arithmetic as it
  is.
- This repository's own facts are proved with `grind`, `simp` and `decide`, which
  are kernel-checked and add no axiom, so each rests on the standard kernel
  principles alone and `ScidoniaTest/Count.lean` asserts exactly that of them.
- Anything derived from a vendored theorem **inherits that theorem's axioms** and
  says so, naming the source. `run_never_exclusive` composes the vendored
  `run_never_frees` with this repository's `not_exclusive_of_neverFreed`, so it
  rests on the vendored theorem's certificate axioms and nothing more, and its
  docstring states which declaration it inherits them from.
  `stuckSt_is_unshared_not_exclusive` is stated through the vendored
  `LEAN_RC_STUCK_ST_eq`, whose list carries no certificate, and says so too.
- A tactic's trust properties belong to the pinned toolchain and to the particular
  proof, not to the tactic or to the goal's shape. `bv_decide` here adds a
  certificate axiom when that proof reaches the certificate step, and two goals
  that look alike can differ: on this toolchain
  `x + 1 > x ∨ x = Int32.maxValue` came out carrying a certificate while
  `rc = 1 → rc + 1 = 2` came out clean, both of them symbolic. The property is
  therefore not predicted from the goal; it is measured. `#print axioms` against
  the pinned toolchain, run before any check relied on it, is what established the
  classification above, and the same probe is owed by any check that depends on
  what a tactic trusts.

## The count of a reference in a presentation

`Scidonia/FracPerm/StateVar/Heap.lean` models one root cell as `Loc → Option σ`
with an opaque state `σ`. It has no vocabulary in which two handles, or two
slots, can name the same object, so it cannot say what a reference count is.
`StateVar/Footprint.lean` adds that vocabulary. A *presentation* lists the live
cells, each an observation leaf of the closed universe — which names no further
reference — or a cell whose *slots* are references; a reference is counted once
per occurrence, so a slot list naming one cell twice contributes it twice.

The count is a definition, not an assumption. `Presentation.occurrences` counts
one reference's occurrences among the live cells' slots, and `refCount p handles
r` is that count plus its occurrences among the handles held outside the store —
the runner's own handle, a caller's binding, a live temporary. `Exclusive p
handles r` is `refCount p handles r = 1`. The facts the write test rests on
follow from the definition: `refCount_single_handle`, that one handle to a
reference no slot names is one live reference; `refCount_pair_of_no_slot` and the
unconditional `not_exclusive_pair`, the take-out pair, whose two handles are two
references whatever the store names; the aliasing pair
`not_exclusive_of_two_occurrences` and `not_exclusive_of_slot_and_handle`; and
`pair_needs_the_drop`, which states the two sides of the discipline theorem at
one presentation. Writing one cell's slots is the elementary step the counts are
read after: `Presentation.setSlots_occurrences` moves the count of a reference by
exactly the changed cell's contribution and leaves every other cell's
contribution alone.

The counted layer composes with what the interface has already proved. The
class's `observe_detached` says a primitive observation of a valid state encodes
without a reference to the root it read, and `StateVar/Heap.lean` carries that
law through a read of the model's root as `read_at_detached`. `Value.refs` is the
references an encoded value names and `noRef_iff_refs_count` reads `NoRef` as
that list's count being zero, so `readAt_result_holds_no_handle` is the
interface's law at the counted layer and `handlesOf_count_eq_zero_of_detached`
says a run whose every issued read result is detached holds no handle on the
root. `refCount_one_of_detached_issues` is the composition: over the modelled
outside-handle list — the runner's own handle and the references the issued
results name, and no other — no slot naming the root and no issued value naming
it leaves that one handle, so the count is one. An outside handle the model does
not list, a caller's binding or a live temporary, is outside the theorem and
would raise the count. `not_exclusive_of_issued_loc` is the same shape with a
value that names the root, whose count is two.

Two readings are hypotheses, not theorems, and the module says so. The first is
that the presentation *is* the live heap — that the cells listed are exactly the
live cells and no live reference is left out; nothing here constructs such a
presentation from a program. The second is `RuntimeAgrees`, that a model state of
one live reference means the count the runtime holds passes
`RefCount.IsExclusive`. It appears only as a hypothesis of the theorems that use
it, no instance of it is constructed in the module or in its checks, and no
bridge from it to the runtime is derived. What the surrounding work does not say
is unchanged: no theorem certifies that a compiled write updates in place, that a
copy happens when it does not, or anything about Lean's object graph, its
allocation, or the compiler's reset/reuse pass. The `Ref`s are `Nat` names into a
list, not addresses, and the counts are logical counts of occurrences, not
machine words. Relating the presentation to a layout's `State d`, so that the
schema's `setLeaf` and take-out have count theorems, is the remaining step of
`FracPerm_Linearity_Proposal.md` §4 S5; the correspondence links of that step
stay outside this module.

`ScidoniaTest/Footprint.lean` is where a client's view of it is checked.

## The counted heap, and the shape the compiler emits

`StateVar/RCHeap.lean` is the step from a count that is a function of the
referencing structure to a count that is state. A cell of the counted heap
carries its slots and a count; `Counted` ties each cell's count to the aliasing
count `Footprint` defines, and `counted_iff_exclusive` makes "count one" and
`Exclusive` the same statement — with `CHeap.WF` (the listed references are
duplicate-free) and `CHeap.Live` (no listed cell has a count of zero) as the two
structural invariants every operation preserves. The operations are the ones the
runtime performs on a count: an allocation, an increment, a non-final decrement,
and a final release that removes the cell, lowers the counts of the cells its
slots named and cascades while any listed cell has reached zero. The update is
the model of the lowering's own test: at a count of one the write is destructive
and the cell keeps its location (`update_preserves_location_of_exclusive`), and
otherwise the updated slots land at a location the heap did not list while the
old cell keeps its slots and loses a reference (`update_copies_of_shared`). The
take-out's temporary is the theorem that matters: the pair's second handle makes
the extracted element's count two, so a write below it copies, and dropping that
handle first restores one, so the same write keeps the location
(`takeout_pair_update_branches`). A location here is a `Ref`, a name in a list
and not a machine address, and the counts are logical occurrences of references:
no theorem here certifies a compiled write, and the compiler's lowering of
`setLeaf` and `set` into this shape is stated as a trusted link rather than
proved.

`StateVar/Run.lean` is the per-run statement. A program is the sequence of steps
a run performs — a read at a path, which returns a value and leaves the heap and
the handle list alone, and a write at a path — and the write step *is* the
executor's schema, defined rather than asserted about: at each array step the cell
at hand is checked, the element is taken out (which is where a handle on the
extracted reference appears), that handle is dropped **before** the focus check,
the extracted focus is checked, the path below is walked in the heap the take-out
left, and the element is put back; at the end of the path the addressed cell's
slots are updated. A step a check turns away does not run at all, so a run is the
sequence of the steps that ran. `Accept` is the invariant a run starts in and
every step preserves: the heap is well formed and live, its counts are the
aliasing counts, and the handles are the runner's own on the session's root
followed by the references the issued read results hold — which name none, because
the sealed observation universe has no location in it, so this is the interface's
own non-escape law rather than a strengthening of it. The per-step theorem
`writeStep_spec` is a structural induction on the path, for an arbitrary depth and
with no fuel, and the per-run theorem `every_write_step_keeps_its_address` is an
induction over the run: for any write in the program of an accepted run, the
address the step resolved to holds the written slots afterwards, which is the
destructive branch, since the copying branch would land them at a fresh location.
The countermodel is the trap: the same schema with the pair's handle still held
writes at a cell of count two and copies, while the same update keeps its location
once the handle is dropped first. What it does not cover: a write whose check
fails is not a step of any run, and the addressed cell's count after a whole step
is not among the conclusions.

`ScidoniaTest/IRShape.lean` is how that link is checked rather than trusted
alone. It reads the post-reference-counting IR the pinned toolchain emitted for
this build — `IR.findEnvDecl` returns a body for a declaration of this library
because these sources carry no `module` keyword, so their oleans hold complete IR
entries rather than `extern` stubs — and asserts the shape the measurement in
`FracPerm_Linearity_Proposal.md` §3.6 records, on one executing path and with the
operand relations bound to a single occurrence selection: the array check's
result is the take-out's array operand, the take-out's extracted focus is the
object the focus check is applied to, that check's result is the recursion's
state operand, and the placeholder write takes the pair's first component at the
index the take-out took the element from.

Two limits are the point of that check rather than gaps in it. For an array
element write the copy-or-mutate decision is not in the IR at all — it is
`lean_is_exclusive` inside `lean_array_uset` / `lean_ensure_exclusive_array` in
the runtime header — so the check establishes that the value reaches the write
owned and nothing about whether the runtime mutates. And what the IR does carry,
`isShared` and a cell `set`, has a specification that requires a count of one for
the store (`Lean.Compiler.IR.Basic`), which is the same count the counted heap
speaks about; whether that count is one where the write runs is a run-time fact
neither instrument carries.

Two toolchain facts this work measured, and the rules that follow from them. A
modelled recursion that a `#guard` or `#guard_msgs` check must evaluate is
written structurally on a fuel or step argument rather than with
`termination_by`/`decreasing_by`: the kernel does not reduce `WellFounded.fix`, so
`decide` gets stuck on a `termination_by` recursion and only a structural one is
visible to it — `CHeap.cascade` is `CHeap.cascadeSteps` at the budget a lemma
shows to be sufficient. And a `run_cmd` whose file retains an earlier elaboration
error may still be elaborated and print a plausible report, so a green report
from a run that also reported an earlier error is void, and a check whose printed
report is its evidence shows that it can fail by being perturbed and observed to
throw. And a term type that carries a list of its own subterms is a **nested
inductive**, on which this toolchain's `induction` will not work ("does not support
the type … because it is a nested inductive type") and `deriving DecidableEq` will
not either ("None of the deriving handlers for class `DecidableEq` applied") — so a
syntax that proofs must induct over is written flat, with scalars and subterms as
direct fields, as `Scidonia/RC/Syntax.lean`'s `Expr` is.

## The pure calculus, its reference-counted image, and the lowering between them

`Scidonia/RC/` formalises the lowering the repository's claim rests on, in the shape
the literature gives it: λ¹ from Reinking, Xie, de Moura and Leijen, *Perceus:
Garbage Free Reference Counting with Reuse* (PLDI 2021) — a pure source calculus, a
reference-counted one, and the strategy between them.

`Syntax.lean` holds the one term type both use: the source constructs, `dup` and
`drop` (which only derivations produce), nodes, and `store` — the write, at a slot
index. It is **flat**, with no list of subterms, because a nested inductive cannot
be inducted on here (see the toolchain facts above). `Pure` is the fragment with no
`dup`/`drop`, the source language; `uses` and `Closed` are its free-variable
account.

`Pure.lean` is the source's semantics: the paper's strict reduction with evaluation
contexts, over *substitution*, and its discipline is **closedness**. Substitution
here is naive and capture-free exactly on closed terms — a term inserted for a
variable has no free variable for a binder to capture — and that is a theorem
(`uses_subst_of_closed`, with `step_preserves_closed` carrying the discipline
through the reduction), not a claim. An open term reduces by the same rules and can
capture; the module says so and exhibits the case. `step_deterministic`,
`value_canonical` and `step_iff_ectx` are the standard facts.

`Lower.lean` is the lowering **strategy**: a syntax-directed derivation from a
borrowed and an owned environment to a target term, `dup` inserted where an owned
variable is used more than once and `drop` where it is unused, proving **totality**
(`lower_total`) and **determinism** (`lower_deterministic`). The splits are
canonical *functions* rather than existentials, which is what makes determinism
true: with an arbitrary split of the environment between two subterms the same
`dup` could be placed on either side and the targets would differ. The relation is
therefore the graph of the canonical strategy — a syntax-directed specialisation of
Figures 5 and 8, not the paper's declarative relation over arbitrary splits — and
the module says so.

`Target.lean` is the target's runtime: a configuration of heap, run handles,
environment, the term's own multiplicity account and the term, with λ¹'s own
evaluation contexts (its heap semantics is context-based) over this repository's
counted heap. `store` is `RCHeap.update` at the subject's cell with one slot set,
so its branch is the heap's own count, and `dup`/`drop` are the count operations.
One limit is stated: a node construction standing alone as a whole program has no
step, the term language having no location form for its result.

`Ownership.lean` is the account the claim needs. `Couple` says the heap is well
formed, its counts are `Counted`'s at the run's handles together with the term's
own references, and each multiplicity pair names **exactly** the reference its
environment binding has (`Bound`, not the weaker "some binding" — the weak form
admits a mis-tagged pair and makes the store theorems arithmetic). `Owns` is
**term-indexed**: it validates the account against the current expression, and a
store step's premise reads the subject's occurrence out of it. `couple_step` carries
the invariant through every step, contexts included. Then the pair that is the
honest form of the claim inside the calculus:

* `store_owned_is_destructive` — a store whose subject the term holds once, with no
  heap slot and no run handle naming that cell, is at a count of one, so
  `RCHeap.update` takes its destructive branch and the cell keeps its location. Two
  of its hypotheses are **not derivable in the module** and are named: no slot
  naming the cell and no run handle naming it are what the discipline's take-out
  provides — `Run.writeStep`'s take-out empties the slot, and the pair's handle is
  dropped before the focus check (`RCHeap.takeout_dropped_count_one`).
* `store_shared_copies` — a store whose subject the account counts above one, or
  whose cell a heap slot also names, is at a count other than one, so the written
  slots land at a fresh location and the old cell keeps its slots and loses a
  reference.

In λRC a store is destructive **exactly when its operand is owned at multiplicity
one**, and a subject another reference also names copies. So that calculus's "every
write in an accepted program is destructive" reduces to "in the lowered term every
store's subject is owned" — a surface-side statement, which is not built here. The run
model states that conclusion for its own writes without this account:
`Run.writeStep_lands` is the per-step statement at an accepted configuration and
`Run.every_write_step_keeps_its_address` the per-run one over a program's execution, and
neither is read through the coupling. What `Transfer.lean` now reads is the two routes at one
configuration of a write step: the coupling at the configuration the step's take-out hands
the nested write (`couple_of_takeout`), and the destructive branch at the nested subject as a
statement about that step (`writeStep_nested_destructive_of_couple`), with `Run.writeStep`'s
own result beside it. What is not built is the induction over a whole program's steps that
would carry the coupling through a run: the composition reads one step's recursion at one
configuration, from an accepted configuration, where `Run.every_write_step_keeps_its_address`
inducts over the program.

`Correspondence.lean` is the link from the typing to those two assumptions of the
store theorems. The typing counts *names* at a store's environment and the store
theorems count a *reference* in the term's own account, so the link is a
correspondence `Corr ρ m Γ` between the target's environment `ρ`, the term's own
account `m` and the typing's environment `Γ`: every pair of the account names the
reference the environment binds its name to (`Bound`, which `Couple` already
carries), the account's multiplicity at each name is the typing's count of that
name, and the account's tags are injective on references (`RefInj`). `bridge` reads
a store's own write clause — its subject owned exactly once — into the write
theorem's two premises, `owns_of_correspondence` is the half of it that needs no
injectivity, and `store_destructive_of_typed` composes the two with
`store_owned_is_destructive`. The injectivity is the clause neither `Typed` nor
`Couple` supplies, and the module exhibits the configuration that separates them:
two names naming one reference, the store typed there, the account `Bound` and
inside `Couple`, and the reference counted twice, so the count of one does not
follow (`couple_does_not_give_count_one`); what would supply it on the environment
side is a distinctness or freshness condition on the environment the program starts
from. `ScidoniaTest/Correspondence` reads the account a
lowered run actually reaches, the correspondence and the composition applied there,
and the affirmative side — the accounts the lowering's prologue and the source's own
environment leave are injective, and the typing refuses the sibling term that would
leave one name twice.

`Transfer.lean` is the link from the run model to that account, and the one module
that sees both: it imports `Correspondence.lean` and
`Scidonia.FracPerm.StateVar.Run`, neither of which imports the other. At a nested write
the take-out has emptied the slot the write lands at and holds the extracted occurrence
as a handle, so the run's handle list is that occurrence followed by the outer handles
while the coupling's split is the outer handles followed by the account's references;
the two read the same references exactly when the account is the extracted occurrence
(`count_takeout_split`, `counted_couple_of_takeout`), and the run's own handle list is
the coupling's split exactly at the empty account (`count_split_agree_iff`).
`Run.exclusive_head` gives the addressed cell no slot naming it and the run's own
handle the only name on it, which are the two hypotheses
`store_owned_is_destructive` names as what the take-out provides, so
`store_destructive_of_takeout` reads the nested write's destructive branch off the
take-out's check, and `store_destructive_of_corr` states the same composition in the
correspondence's own vocabulary: it takes the correspondence's name counts beside the
coupling, builds `Corr ρ m Γ` from the coupling's `Bound` and the injectivity the two
countings give, and reads the write theorem's two premises off the built structure, so no
injectivity proof is an input. The injectivity is not one of the first theorem's inputs
either: the run's counting beside the coupling's counting of one heap force the account
to be the one extracted occurrence (`expand_eq_singleton_of_counted`), and one
occurrence's tags are injective whatever they are (`refInj_of_counted`), which is what
`ScidoniaTest/Transfer`'s `acct_inj` reads at the take-out. `refInj_not_determined` is
the boundary: two accounts with the same references are one configuration to the run's
side — the same count at every heap and handle list — and one of them names a reference
twice. `ScidoniaTest/Transfer` reads the transfer at a heap the take-out has emptied,
the composition applied at the run's own handle list and again there through the
correspondence, beside `store_destructive_of_typed` at the coupling's split, and that
boundary at one heap and one handle list.

The same module now reads the run's own write. `couple_of_takeout` is the coupling at the
configuration `Run.writeStep`'s recursion hands the nested write: the run's counting at the
level (`Run.takeOut_counted`) beside the schema's focus check there gives the coupling whose
handles are the level's handle list and whose account names the extracted occurrence — the
account's identity `expand m = [e]` is that theorem's hypothesis, since it is the coupling
being built and the counting the identity would otherwise be read from does not exist yet —
and the account is read *out of* the run's handle list rather than added beside it, which
`couple_at_run_handles_is_empty` is why (`count_split_agree_iff` at the coupling's split).
The identity is derived where an already-built coupling is at hand:
`store_destructive_of_takeout` and `store_destructive_of_corr` hold the coupling, whose own
counting is the second counting, so `expand_eq_singleton_of_counted` reads the identity off it
beside the run's counting and the identity is no input of theirs.
`writeStep_focus` and `writeStep_recurses` read the schema's own check and recursion off the
step — the pair's drop cancels the increment, so the check the schema makes is the one the
take-out's result carries, and the step's result is the put-back of the recursion's — and
`writeStep_nested_destructive_of_couple` composes: a write step of an accepted configuration,
its take-out, the account through the coupling, and the schema's checks are the write
theorem's two premises, so the destructive branch at the nested subject is a statement about
that step, with `Run.writeStep_spec`'s own result beside it and `Corr`'s injectivity clause
built from the two countings (`store_destructive_of_corr`) rather than carried.
`writeStep_subject_destructive_of_couple` is the same at a write whose path's level is its
last, where the recursion's entry is the write's subject and the leaf's check supplies the
write rule's premise on the written slots, so the two routes' conclusions are about one cell.
The induction over a whole program's steps is `Run.every_write_step_keeps_its_address`'s own;
the composition reads one step's recursion at one configuration.

`Discipline.lean`'s `Runs` and this correspondence are two routes and not one.
`Runs` is a target-side sufficient condition *at a store*, which `runs_store_owned`
reads the write's two hypotheses off, and it is not the link from a typing: the
source of `ScidoniaTest/Target` is typed at `[]`, `[0, 1, 2]` and its canonical
lowering is not judged, because `Runs.bindVal` demands the resumed write at every
reference the binder could take and the instance at `r = 2` counts that reference
three times — `source_typed` beside `lowered_not_runs`. The correspondence is read
at the configuration the run does reach, where the judgement holds as well, and
`ScidoniaTest/Correspondence` reads both there. `Typing.lean` is the source side the
correspondence is stated against: the lowering's environment discipline read as a
typing, with the write's clause strengthened to the subject's ownership.

What is *not* claimed: no theorem relates the two calculi semantically — that the
target's reduction preserves the source's, or that it is garbage free — so the
lowering is shown to be a total deterministic strategy and not a correct one; and
nothing here is about compiled code. The runtime's own decision is
`lean_is_exclusive` inside `lean_array_uset`, the compiler's lowering of this
repository's write paths into this shape is checked by `ScidoniaTest/IRShape.lean`
and otherwise trusted, and the `Ref`s are names in a list, not addresses.

`Paper/lowering.tex` is the paper on this material: the counted heap, the two
calculi, the lowering strategy, the account and the two store theorems, and then
the typing that puts the count where a write needs it — its write clause, the two
conditions a written name carries, the four shapes with a second holder of the cell
refuted beside their typed companions, the correspondence that reads the typing's
count of a name into the write theorem's count of a reference, and the two routes
read at one step of an accepted run — with the prose kept to what each step is for.
It is built with `pdflatex` through `latexmk` — twice, for the bibliography — and
the built `Paper/lowering.pdf` is committed beside it, as the companion paper's is.
Every Lean quotation in it is a `\codeframe` range of the library with a
`%!check:` fragment beside it, as the companion's are, so the excerpts are checked
rather than hand-quoted: a range that drifts is a `check-listings.py` failure and
not a silent misquotation. One build fact is worth recording, because it cost time
to find: `fontspec` cannot find any font by name or by path in this environment, so
the paper is built with `pdflatex` rather than `lualatex`, which forbids Unicode
outside the quoted frames. The prose therefore uses math mode for symbols, and the
Unicode in the frames is mapped to font commands in the preamble by
`newunicodechar` — a character in a quoted range with no mapping fails the build,
which is the signal to add one.

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
  --prose Slides/models.md \
  --prose Slides/lawful.md \
  --example Slides/LawfulBuffer.lean \
  --prose Slides/universe.md \
  --example Slides/NoRefEverywhere.lean \
  --prose Slides/sealed.md \
  --prose Slides/outlook.md \
  --title "Fractional permissions in Lean 4" \
  --subtitle "Erased ghost state, Hoare monads and in-place update" \
  --output Slides/fracperm.html
```

The prose format and the panel rules are those of the generator, documented in
`../vericoding-tutorial/AGENTS.md`. A panel fenced ```` ```lean ```` is compiled, so
it is the way to quote *compiled* code: a class is restated and then built from a
library value, and a definition's clauses are stated by `rfl`. A panel fenced
```` ```@path ```` must be a verbatim excerpt of a file, and its path resolves
through the generator's repository root, so this repository's source is quoted as
```` ```@../lean/Scidonia/… ````; a quotation shows a definition exactly as the
library has it and fails the build if the library changes. The prose format has
no table syntax — a `|`-table renders as literal text, so use bullets — and every
fenced block is either quoted or compiled, so an excerpt of generated C or of an
IR trace belongs in inline code within a bullet, with the command that produced
it, not in a fence. The built
`Slides/fracperm.html` is committed, so the deck can be viewed on GitHub Pages
at https://scidonia.github.io/lean-examples/Slides/fracperm.html; rebuild it
and commit it with any change to the deck's sources.

A second, self-contained tutorial builds the kit of a *write* from the
definitions and then shows when the write stays in place. It needs no test
library beyond the first command above:

```sh
nix develop -c lake env python3 ../vericoding-tutorial/scripts/build_deck.py \
  --prose Slides/update-kit.md \
  --example Slides/UpdateSteps.lean \
  --prose Slides/update-behaviour.md \
  --title "Writing through a path" \
  --subtitle "How a pure update becomes a mutation, and how to make it legal" \
  --output Slides/update.html
```

`Slides/update.html` is committed too, and viewable at
https://scidonia.github.io/lean-examples/Slides/update.html. Its
"twelve shapes" slide and its excerpts of the emitted code are measurements,
not checked panels: the Lean panels around them are compiled, and the address
assertions that ship live in the `inplace` harness.

## Paper

`Paper/` holds the two papers on this work:

| Path | Contents |
| --- | --- |
| `unobservable-effects.tex` | The permissions companion's source |
| `unobservable-effects.pdf` | The built companion, committed so it reads without a TeX installation |
| `lowering.tex` | The source of the counted heap and the typing |
| `lowering.pdf` | The built paper, committed for the same reason |
| `frames/` | The frames, generated: one comment-free copy of a quoted range per file, plus `lookup.tex` mapping a range to its file. Do not edit by hand |
| `laws.tex` | The law frames, generated from the library by `gen-laws.py`; do not edit by hand |
| `counts.tex` | The numbers the two papers' prose states about the library and about their own panels, generated by `gen-laws.py`; do not edit by hand |
| `gen-laws.py` | Locates each law's statement by line range, and writes `laws.tex` and `counts.tex` |
| `gen-frames.py` | Writes the frames the papers ask for, with `leanstrip.py` |
| `leanstrip.py` | Removes Lean comments (nested block comments, line comments, strings) |
| `check-listings.py` | Verifies every frame in the papers against the library, and the generated counts against it |

The papers build with `pdflatex`, and their Lean frames are syntax-highlighted by
`minted`, reading each frame through Pygments' Lean lexer under the
`gruvbox-light` style — the light styles differ mostly in how much colour they
spend, and the dark ones (`one-dark`, `monokai`, `dracula`, `lovelace`) paint
identifiers near-white, which vanishes on paper. Two consequences for the build:
they need `-shell-escape` for minted to run `pygmentize`, and they need Pygments on
`PATH`. `_minted-<jobname>/` holds minted's cache and is ignored by git; deleting
it only costs a slower rebuild.

A frame is written `\codeframe[linerange=lo-hi]{../path}`, naming the source and
not the frame: the preamble's `frames/lookup.tex` turns that range into
`frames/<key>.lean`, and a range with no generated frame is a build error. A
single-line frame is written `lo-lo`; a call in any other shape is one no frame
can be made for, and both `gen-frames.py` and `check-listings.py` report it rather
than passing it over, because the `%!check:` directive beside it would otherwise be
paired with whatever frame follows. The frame is that range with its comments
removed, so a doc comment between two constructors does not appear, and a range
that begins inside a doc comment does not leak the tail of it. Each frame is set in
an unbreakable box, so it cannot be split across a page: a frame too tall for the
space left moves to the next page, and the build reports an overfull vbox if a
frame were taller than a page. `gen-frames.py` owns `frames/`, so a frame no call
names is deleted when the generator runs: a moved range is a deletion and an
addition, not a second copy beside the first. The toolchain's `lualatex` cannot
load its font loader, so `pdflatex` it is, and the Unicode in the quoted Lean is
mapped to font commands in each preamble by `newunicodechar`, one character per
package line. A character in a quoted range with no mapping fails the build, which
is the signal to add one.

```sh
cd Paper
python3 gen-laws.py                       # law frames and counts, after a library change
python3 gen-frames.py                     # the frames themselves
latexmk -pdf -shell-escape unobservable-effects.tex   # the permissions companion
latexmk -pdf -shell-escape lowering.tex               # the counted heap and the typing
python3 check-listings.py                 # every frame and count, against the library
```

Every frame is a line range into the library, so a paper quotes the source
rather than a transcription of it, and a range that has drifted is a check
failure rather than a silent misquotation. `check-listings.py` checks a panel
against a fragment the marginal `%!check:` directive names, a law frame against
the declaration it names, and a generated frame against the range it was made
from, recomputing the comments-removed text. It also recomputes `counts.tex` and
fails when that file is not the count the library gives, naming the file to
regenerate; each paper's prose reads its numbers — the theorems the library
publishes, and the panels it and the appendix quote — from that file rather than
stating them, so a count that moves with the library is regenerated rather than
corrected by hand. The panel counts are per paper, so the two do not share a
numeral: `\panelcount` is the companion's, and the lowering paper reads its own
count under that name through a `\let` in its preamble. Nothing here compiles the
Lean: the library is built separately, and the papers' measurements are the
`inplace` harness's.

The description, observation and layout universes are quoted in the body, where
they are defined, rather than in the appendix, so each is shown once.

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
| `Scidonia/FracPerm/StateVar/Description.lean` | The description universe: `Desc`, `El d`, and `slotDesc` |
| `Scidonia/FracPerm/StateVar/Universe.lean` | One instance for every description: `encodeEl`, its two laws, `Described d`, `describedStateVar d`, and `transport` |
| `Scidonia/FracPerm/StateVar/Slot.lean` | The slot: `encode`/`decode`, both inverse laws, and the instance transported at `slotDesc` |
| `Scidonia/FracPerm/StateVar/Layout5.lean` | Model 5: the observation universe and layouts, paths, the zipper, `read?`/`setLeaf`, and the lawful adapter |
| `Scidonia/FracPerm/StateVar/Sealed.lean` | `SealedStateVar`: a layout state's type as the whole interface, with the read and the write defined by the library and the derived lawful instance |
| `Scidonia/FracPerm/StateVar/RefCount.lean` | The reference count as a write sees it: the model of `lean_inc_ref_n`/`lean_dec_ref` vendored from Lean 4, `IsExclusive`/`IsUnshared`, and the counter-level facts the write discipline rests on |
| `Scidonia/FracPerm/StateVar/Footprint.lean` | The count of a reference in a presentation of the heap: `Ref`, `Node`, `Presentation`, `occurrences`/`refCount`/`Exclusive`, the take-out pair and aliasing facts, `Presentation.setSlots_occurrences`, the composition with `NoRef`, and `RuntimeAgrees` stated as a hypothesis |
| `Scidonia/FracPerm/StateVar/RCHeap.lean` | The counted heap the lowering works over: `Cell`, `CHeap`, `Counted`/`WF`/`Live`, the allocation, increment, non-final decrement, final release and its cascade, and the update whose branch is the heap's own count |
| `Scidonia/FracPerm/StateVar/Run.lean` | The per-run statement: the step sequence a run performs, the executor's write schema as a definition, the acceptance invariant, the per-step and per-run destructive-write theorems, and the un-dropped-pair countermodel |
| `Scidonia/RC/` | The formalisation of the lowering: a pure calculus, a reference-counted one, the strategy between them, and the target runtime with its ownership account |
| `Scidonia/RC/Syntax.lean` | The one flat term type both calculi use — the source constructs, `dup`/`drop`, nodes and the write — with `Pure`, `uses` and `Closed` |
| `Scidonia/RC/Pure.lean` | The source semantics: strict reduction with evaluation contexts over substitution, its closedness discipline, determinism and canonicity |
| `Scidonia/RC/Lower.lean` | The lowering strategy: the syntax-directed derivation with its canonical splits, and its totality and determinism |
| `Scidonia/RC/Target.lean` | The target runtime: configurations over the counted heap, λ¹'s evaluation contexts, and `store` as `RCHeap.update` |
| `Scidonia/RC/Ownership.lean` | The coupling invariant, the term-indexed ownership relation, and the two store theorems |
| `Scidonia/FracPerm/InPlace.lean` | The optional run-time check the in-place check calls |
| `Scidonia/FracPerm/Counter.lean` | The worked second object: a count and a log, and the check that covers both |
| `ScidoniaTest/` | Compile-time checks, built as the `ScidoniaTest` library |
| `ScidoniaTest/Structured.lean` | The structured interface's protocol and sealing checks |
| `ScidoniaTest/StateVar.lean` | The generic state variable's witness, model, bridge, and negative-law checks |
| `ScidoniaTest/Universe.lean` | The description universe's encoding, instance, model, and transport checks |
| `ScidoniaTest/Slot.lean` | The slot's correspondence, instance, snapshot, shape-change, and detector checks |
| `ScidoniaTest/Model5.lean` | Model 5's reads, zipper laws, frames and snapshots, the whole-array rejection, and the old class's countermodel |
| `ScidoniaTest/Sealed.lean` | `SealedStateVar`'s reads, writes and theorems at its instances, the rejection of an `observe`/`encodeRead`/mismatched-`rep` instance, and the countermodel comparison |
| `ScidoniaTest/Count.lean` | The count module's controls — the two tests on counts that tell them apart, the hazard pair `1 → 2 → 1`, and the take-out at the counts a one-reference cell hands out — and `#print axioms` on the representative theorems |
| `ScidoniaTest/Footprint.lean` | The counted presentation's controls — evaluated counts with a pinned control beside each, the aliased-cell and second-handle countermodels with an affirmative counterpart at the same presentation, the composition with detachment, and the reverse runtime link pinned by the message `#check` emits |
| `ScidoniaTest/RCHeap.lean` | The counted heap's controls — evaluated counts and both branches' locations, the duplicate-key and zero-count countermodels with affirmative counterparts at the same heap, and asserted axiom lists |
| `ScidoniaTest/IRShape.lean` | The check over the compiler's own output: the post-reference-counting IR of the write paths read with `IR.findEnvDecl`, the shape and operand relations required of it on one executing path, and the borrowed-get control |
| `ScidoniaTest/Run.lean` | The run model's controls — evaluated steps and resolutions with a pinned control beside each, the held-pair copies and dropped-pair keeps pair at one heap and path, and asserted axiom lists |
| `ScidoniaTest/RC.lean` | The calculus's controls — evaluated steps and translations with a control beside each, the capture pair, and asserted axiom lists |
| `ScidoniaTest/Target.lean` | The target's controls — evaluated runs with controls, the owned store keeping its location beside the shared store copying at one heap and term, and asserted axiom lists |
| `ScidoniaExamples/` | Worked examples of the fractional-permission interface, built as the `ScidoniaExamples` library |
| `ScidoniaExamples/Structured.lean` | Worked examples of the structured interface |
| `ScidoniaInPlace/` | The `inplace` executable: run-time checks of the in-place update |
| `Slides/` | The slide deck's sources: prose series and stepped proofs |
| `Paper/` | The two papers: their sources and built PDFs, and the tools that keep their quotations to the library |
| `Main.lean` | Entry point of the `scidonia` executable |
