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
  --example Slides/NoRefEverywhere.lean \
  --prose Slides/outlook.md \
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
| `Scidonia/FracPerm/StateVar/Description.lean` | The description universe: `Desc`, `El d`, and `slotDesc` |
| `Scidonia/FracPerm/StateVar/Universe.lean` | One instance for every description: `encodeEl`, its two laws, `Described d`, `describedStateVar d`, and `transport` |
| `Scidonia/FracPerm/StateVar/Slot.lean` | The slot: `encode`/`decode`, both inverse laws, and the instance transported at `slotDesc` |
| `Scidonia/FracPerm/StateVar/Layout5.lean` | Model 5: the observation universe and layouts, paths, the zipper, `read?`/`setLeaf`, and the lawful adapter |
| `Scidonia/FracPerm/StateVar/Sealed.lean` | `SealedStateVar`: a layout state's type as the whole interface, with the read and the write defined by the library and the derived lawful instance |
| `Scidonia/FracPerm/InPlace.lean` | The optional run-time check the in-place check calls |
| `Scidonia/FracPerm/Counter.lean` | The worked second object: a count and a log, and the check that covers both |
| `ScidoniaTest/` | Compile-time checks, built as the `ScidoniaTest` library |
| `ScidoniaTest/Structured.lean` | The structured interface's protocol and sealing checks |
| `ScidoniaTest/StateVar.lean` | The generic state variable's witness, model, bridge, and negative-law checks |
| `ScidoniaTest/Universe.lean` | The description universe's encoding, instance, model, and transport checks |
| `ScidoniaTest/Slot.lean` | The slot's correspondence, instance, snapshot, shape-change, and detector checks |
| `ScidoniaTest/Model5.lean` | Model 5's reads, zipper laws, frames and snapshots, the whole-array rejection, and the old class's countermodel |
| `ScidoniaTest/Sealed.lean` | `SealedStateVar`'s reads, writes and theorems at its instances, the rejection of an `observe`/`encodeRead`/mismatched-`rep` instance, and the countermodel comparison |
| `ScidoniaExamples/` | Worked examples of the fractional-permission interface, built as the `ScidoniaExamples` library |
| `ScidoniaExamples/Structured.lean` | Worked examples of the structured interface |
| `ScidoniaInPlace/` | The `inplace` executable: run-time checks of the in-place update |
| `Slides/` | The slide deck's sources: prose series and stepped proofs |
| `Main.lean` | Entry point of the `scidonia` executable |
