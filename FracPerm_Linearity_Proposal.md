# Ensuring linearity: findings and a proposal

Status: proposal for discussion. Repository `Scidonia/lean` (`master`), Lean `4.35.0-rc3`, core + `std`.
Scope: what our fractional-permission work actually establishes, where linearity fails to hold, and five steps that would close the gap, in increasing cost.

## 1. The question

We wanted a pure language with mutable programming: keep one reference and the runtime updates in place, share it and it copies. The question this document answers is whether fractional permissions can *ensure* the "one reference" condition, and if not, what would.

## 2. What exists today

| Model | Interface | State |
| --- | --- | --- |
| 1 | `Reader`/`Program`, sealed trees, `runFresh` the only runner (`Scidonia/FracPerm/Structured/`) | one `UInt64` array, hidden |
| 2 | `LawfulStateVar`: laws as proof fields (`StateVar/Class.lean`) | any type that proves them |
| 3 | `Slot` by a description universe (`StateVar/{Description,Slot}.lean`) | a slot, via `encode`/`decode` |
| 4 | one instance for every description (`StateVar/Universe.lean`) | `Described d`, and anything isomorphic |
| 5 | layouts, paths, take-out writes, `SealedStateVar` (`StateVar/{Layout5,Sealed}.lean`) | arrays of structs, nested arrays |

Current standing of the claims:

- **Proved** (kernel-checked, no `sorry`, only Lean's three standard axioms): the permission protocol (a write needs `held = 1`; a read needs its ledger entry; every fraction returned exactly once); share conservation, exclusion, joins, schedule independence, replay; detached reads *in the modelled encoding* (`NoRef`); snapshots and frames; `setLeaf` equals the zipper's path replacement. For the layout universe, `encodeObs` is injective and location-free for every observation description, and a whole-array read has no `ObsPath` at all.
- **Structural** (design property of the interface, checked by refused probes): no public route reaches a session's array; `SealedStateVar` instances supply no read and no encoding, so the leaking instance cannot be written.
- **Measured** (compiled, asserted, per exercised path): whether a write updates in place. Cases: `structured-unique`, `structured-closure`, `sealed-unique`, `layout5-unique`, `layout5-nest`, and their `*-checked-*` children; controls that must copy: `shared-copies`, `literal-copies`, `layout5-shared-copies`, `layout5-nest-aliased`.
- **Trusted**: the compiler, the runtime, and the library's own primitives. The repository says so: "updating is run-time evidence and not a theorem" (`AGENTS.md:228`), "no theorem here certifies that a compiled write updates in place" (`AGENTS.md:332`), "[in-place is] not a theorem. Two instruments report it" (`StateVar/Layout5.lean:60`).

## 3. Findings

### 3.1 "Linearity" is four different properties

They are routinely conflated, and only some are achievable by permissions:

| Property | Meaning | Mechanism that can give it |
| --- | --- | --- |
| **L1 permission linearity** | each fraction taken out is returned exactly once; no write while readers are out | the ghost ledger, statically (proved) |
| **L2 authority uniqueness** | at a write, no reader may read | `held = 1`, statically (proved) |
| **L3 reference uniqueness** | at a write the object has reference count 1 | sealing + read-result discipline (structural), assertions (measured) |
| **L4 in-place update** | the write actually mutates rather than copies | L3 *and* an update shape the compiler's reset/reuse can exploit |

The ledger gives L1 and L2. It does not give L3, because the ledger is ghost state in `Prop` while reference counts are a runtime notion: the logic cannot see pointers.

### 3.2 Authority is not reference

A write requires `held = 1`, so no reader is out. That says nothing about how many pointers into the object exist. Three routes defeat the inference:

1. **The caller's binding.** `HSt.exec m s hp hq` takes the state from the caller. A caller that still holds `s` has two references; the write copies. Measured: `shared-copies`.
2. **A read result that shares memory.** A reader may return its fraction honestly and keep the value it received. If that value shares mutable structure with the state, the next write copies. This is what Model 5 closes: reads end only at observation types (`ObsDesc`), which contain no array and no struct of the state, and the encoding has no `.loc` case.
3. **The library's own temporaries.** The executor's take-out pair is a second reference to the extracted element, and it defeated the exclusivity check on first writing (see 3.5).

### 3.3 A lawful instance can still leak

`LawfulStateVar` asks the author for `observe` and `encodeRead`. `ScidoniaTest/Model5.lean` exhibits `leakyArrayStateVar`, whose `observe () s := s` returns the protected array itself, with a constructor-faithful injective encoder that produces no `.loc`; all four laws hold (`leakyArray_read_returns_state`, `leakyArray_encoding_of_two`). So lawfulness as stated constrains the *encoding*, not the object graph, and `NoRef` is a statement about the encoding only.

`SealedStateVar` closes this by construction: an instance supplies only a layout and `rep : σ = State layout`, and the library fixes `Result` and `encodeRead` (`rfl`). Supplying an `observe` or `encodeRead` field is rejected by elaboration, and `SealedStateVar.observe` is not a name a client can write (`ScidoniaTest/Sealed.lean`).

### 3.4 What sealing already closes

`runFresh` creates the state inside; no public route returns it (probes refuse `«open»`, `plug`, `Context`, `takeOut`, `plugAt`, `setAt`, `inBounds`, and the private executor). Reads return `Option Value`. So for client code, "no reader is out" does coincide with "one reference" — which is why the sealed harness cases are in place.

### 3.5 Compiler facts we measured, each of which cost a false claim

| Observation | Evidence |
| --- | --- |
| An array captured by `Task.spawn` is marked thread-shared; `lean_is_exclusive` is false for it thereafter, and the first write after the join copies | measured; `AGENTS.md:244` |
| A compiled array *literal* is a persistent object, never exclusive, so it always copies | `literal-copies` |
| Identical expressions (`Array.replicate n 0` twice) are merged, leaving one shared array | measured in the first in-place spike |
| A projection kept alive across a run (reading `s.log`'s address first) makes the write copy | harness fix recorded in `ScidoniaInPlace/Main.lean` |
| **Trap 1.** The take-out returns `(array, element)`; while that pair is live the element has two references, so the focus check fired on a unique array | `layout5-checked-unique` failed; after destructuring, the generated C releases the pair before the check |
| **Trap 2.** With the update returning `State d × Bool`, reset/reuse fired but on the *transient* pair: the object stored back was a fresh allocation, so the struct copied even though `lean_is_exclusive` + `lean_ctor_set` appear in the C | `layout5-unique` measured a changed address; fixed by making the update state-only (`StateVar/Layout5.lean:37`, `:685–716`) |

Two lessons: the C containing reuse is not evidence about the object that matters, so in-place claims need address assertions; and the update's *shape* decides reuse, so it is an obligation on instance and library authors, not on the permission discipline.

## 4. Proposal: five steps, cheapest first

### S1 — Seal the program surface so the state type is unnamed

Today `SealedStateVar.setLeaf p x : σ → σ × Bool` is public and `σ` is the client's own type, so `State layout` still appears in client code. Expose instead a sealed program over a layout:

```lean
Program (d : Layout) α          -- pure | get (ObsPath d) k | set (ObsPath d) x k
Reader  (d : Layout) α          -- pure | get … | size … | parallel l r k
runFresh : Init → Program d α → IO α
```

Private trees, private interpreter, `runFresh` the only runner — Model 1's sealing with Model 5's descriptions and take-out writes.

- **Buys:** the client cannot name the state, so the only references are the library's. Removes routes 1 and 2 above by construction.
- **Cost:** a new surface plus its checks; the interpreter is new code that must keep the one-reference discipline (S2).
- **Note:** with the state unreachable, the fractions are no longer what gives write exclusivity — the type structure does. The fractions remain the *sharing* accounting: how a fork splits authority, why a join waits, and the interleaving theorem.

### S2 — Library-side obligations, asserted per instance

The interpreter's own code must not add a reference on the write path: destructure the take-out pair before the check; thread the new focus as a value, never as a closure; return the state alone so reset/reuse can rewrite the struct cell; avoid holding a projection across the recursion.

- **Buys:** makes S1's uniqueness real rather than nominal, for the paths exercised.
- **Cost:** discipline in the interpreter, plus per-instance harness cases with address assertions. Already done for Models 1 and 5; this step generalises it.

### S3 — A deep uniqueness check in checked mode

`SCIDONIA_CHECK_INPLACE=1` currently tests the top-level object (and, for `Counter`, the log). Extend it, for a known layout, to walk the *state's mutable footprint* and require count 1 at every mutable node, at each write.

- **Buys:** catches nested sharing (a spare slot aliasing an element) that a top-level test cannot see; independent of the instance author.
- **Cost:** O(footprint) per check, and false alarms when immutable parts are deliberately shared.

### S4 — Check the compiled code at definition time

Lean's IR, after reference counting is inserted, is available during elaboration (`IR.findEnvDecl`). Add an attribute that runs a small alias analysis over the executor's and an instance's generated code and refuses code that (a) increments the state into a result, or (b) passes a still-referenced cell into an in-place mutation.

- **Buys:** covers what the compiler actually emits, so it catches Trap 1 and Trap 2 mechanically rather than by two hand-written assertions.
- **Cost:** a checker, not a proof; it must be maintained against Lean's IR.

### S5 — Prove uniqueness against a counted heap

Model the heap with reference counts (λRC, from Ullrich and de Moura, *Counting Immutable Beans*), state the sealing assumptions as hypotheses — the object never escapes, every read result is built from the observation universe — and prove: authority 1 at a write implies exactly one reference in the model.

- **Buys:** turns L3 from "structural plus measured" into a theorem *about the model*, with the assumptions explicit.
- **Cost:** research-scale, and a residual trust boundary that must be stated: the correspondence between the model and the compiled primitives (a verified translation, or an explicitly trusted one), plus Lean's IR-to-C step.

### What cannot be done in Lean

Value linearity cannot be enforced: Lean has no affine or uniqueness types, so a client holding a value of a type can copy it. Rust's borrows, Clean's uniqueness types and Linear Haskell enforce L3 statically in the type system; Lean must buy it with sealing (S1), assertions (S2, S3) and, at best, a model (S5). This is a property of the host language, not of the permission theory.

## 5. Recommended order

1. **S1 + S2** as one milestone: they are inseparable, since S1's claim rests on the interpreter keeping one reference, and S2 is what makes that true and checked. This is the step that makes "linearity of access" true for client code.
2. **S4** next: cheapest mechanical protection against the two traps, and it covers code a human will not re-read.
3. **S3** where a layout is available: nested-footprint checking.
4. **S5** as the research goal, with its trust boundary stated up front.

## 6. Evidence each step should add

| Step | Acceptance evidence |
| --- | --- |
| S1 | refused probes for every raw-state route (as `ScidoniaTest/Model5.lean` does), plus a `#guard_msgs` that the state type is not nameable in client code |
| S2 | harness cases with address assertions on the array and on the focused cell, unique and aliased; the aliased case must abort under the check |
| S3 | a case with a deliberately aliased nested element: unique case passes, aliased case aborts naming the nested site |
| S4 | the checker rejects a deliberately bad instance (a closure kept, a pair not destructured) and accepts the shipped ones |
| S5 | the theorem statement with its hypotheses listed, plus an explicit list of what remains trusted |

## 7. Open questions

1. Is S1's strictness worth losing a client-visible `State`? It buys the strongest form of "you never hold the state", but it also removes the ability to run the operations on one's own value.
2. Should the ledger's role be stated plainly as *sharing* accounting (parallel safety), with uniqueness owned by sealing? That is a change in the pitch, not in the code.
3. For S4, is a checker on Lean's own IR acceptable tooling to maintain, or is that effort better spent on S5's model?
4. Does S5 need a verified translation to be worth publishing, or is "proved in the model, correspondence trusted and stated" the honest and sufficient result?

## 8. Non-claims

- No theorem here certifies in-place update for compiled code, and none certifies anything about Lean's object graph.
- `NoRef` is about the modelled encoding. `SealedStateVar` removes the author's ability to choose that encoding; it does not prove the library's encoding matches runtime references.
- Copying in Lean is always safe: a missed in-place update costs time, never correctness or a race.
- The fork/join is notional; the executor is sequential, and a real concurrent backend would still face the thread-shared marking of `Task.spawn`.

## 9. Pointers

- `AGENTS.md:228, 332, 456, 466, 559` — what is proved, and what is only runtime evidence.
- `Scidonia/FracPerm/StateVar/Layout5.lean:37, 46, 57, 60, 63, 685–716` — the take-out, the checks, the update shape.
- `Scidonia/FracPerm/StateVar/Sealed.lean` — the sealed class, its derived laws and instances.
- `ScidoniaTest/Model5.lean` — the leaking lawful instance and the refused raw-state routes.
- `ScidoniaTest/Sealed.lean` — the refusals that make sealing structural.
- `ScidoniaInPlace/Main.lean` — the harness cases and their address assertions.
