# Ensuring linearity: findings, options and a proposal

Status: proposal for discussion. Repository `Scidonia/lean` (`master`), Lean `4.35.0-rc3`, core + `std`, this toolchain's x86-64 Linux compiler.
Scope: what our fractional-permission work establishes, where linearity fails, and what could close the gap. **The model is single-threaded:** `parallel` in the structured interface is notional (a fork/join *semantics*), the shipped executor runs branches one after another, and no task, thread or scheduler primitive is used. Nothing here depends on concurrency, and the one concurrency observation in §3.4 is a boundary note about a direction not taken.
Claim discipline used throughout: every statement is labelled **proved** (kernel-checked), **structural** (a property of the exported surface, shown by refused probes), **measured** (a named harness case on this toolchain) or **trusted** (compiler, runtime, library primitives). Measured claims are measured *on the paths named*, and generated-code inspection is compiler evidence, not proof.

## 1. The question

We want mutable programming in a pure language: keep one reference and the runtime updates in place; share it and it copies. Can fractional permissions *ensure* the "one reference" condition — and if not, what would?

## 2. What exists today

| Model | Interface | State |
| --- | --- | --- |
| 1 | `Reader`/`Program`, sealed trees, `runFresh` the only runner (`Scidonia/FracPerm/Structured/`) | one `UInt64` array, hidden |
| 2 | `LawfulStateVar`: laws as proof fields (`StateVar/Class.lean`) | any type that proves them |
| 3 | `Slot` by a description universe (`StateVar/{Description,Slot}.lean`) | a slot, via `encode`/`decode` |
| 4 | one instance for every description (`StateVar/Universe.lean`) | `Described d`, or anything isomorphic |
| 5 | layouts, paths, take-out writes, `SealedStateVar` (`StateVar/{Layout5,Sealed}.lean`) | arrays of structs, nested arrays |

**Proved.** The permission protocol (a write needs `held = 1`; a read needs its ledger entry; every fraction returned exactly once); share conservation, exclusion, joins, schedule independence and replay over the structured semantics; detached reads *in the modelled encoding* (`NoRef`); snapshots and frames; `setLeaf` equals the zipper's path replacement. In the layout universe, `encodeObs` is injective and location-free for every observation description, and a whole-array read has no `ObsPath`.

**Structural.** No public route reaches a session's array; `SealedStateVar` instances supply neither a read nor an encoding, so the leaking instance cannot be written. Both are shown by refused probes, which establish the *shape of the exported surface*, not anything about reference counts.

**Measured, on the named cases of this toolchain.** Whether a write updates in place: `structured-unique`, `structured-closure`, `sealed-unique`, `layout5-unique`, `layout5-nest` and their `*-checked-*` children; controls that must copy: `shared-copies`, `literal-copies`, `layout5-shared-copies`, `layout5-nest-aliased`. All in `ScidoniaInPlace/Main.lean`.

**Trusted.** The compiler, the runtime, and the library's own primitives. Stated in the repository: "updating is run-time evidence and not a theorem" (`AGENTS.md:228`); "no theorem here certifies that a compiled write updates in place" (`AGENTS.md:332`); "[in-place is] not a theorem. Two instruments report it" (`StateVar/Layout5.lean:60`).

## 3. Findings

### 3.1 "Linearity" names five different properties at four different layers

The conflation is the source of the whole difficulty:

| Property | Layer it lives at | Statement | Established by |
| --- | --- | --- | --- |
| **L1 fraction discipline** | the permission model (ghost ledger, in `Prop`) | each fraction taken out is returned exactly once; `exec` demands `held = 1` at the end | proved |
| **L2 authority uniqueness** | the permission model | at a write, no reader may read (`held = 1`) | proved |
| **L3 no client alias** | the safe API surface | no exported operation returns the session's state, or a mutable subtree of it, to a client | structural (private constructors and interpreter; refused probes), under the exclusions in §4 S1 |
| **L3′ runtime reference uniqueness** | the runtime object graph | at a write, the object has count 1 — *at the root* (the array) or *over the mutable footprint* (every node a write can mutate) | measured per path; **not** implied by L1, L2 or L3 |
| **L4 in-place update** | the compiled update | the write mutates rather than allocates | measured, compiler-dependent; requires L3′ *and* an update shape the reset/reuse pass can exploit — it does not follow from L3′ alone |

So L1 and L2 are theorems about a model; L3 is a property of an interface; L3′ and L4 are runtime and compiler facts about compiled code.

### 3.2 Authority is not reference

`held = 1` says no reader is out. It says nothing about how many pointers into the object exist, because the ledger is ghost state while counts are runtime state. Three routes defeat the inference:

1. **The caller's binding.** `HSt.exec m s hp hq` takes the state from the caller; a caller still holding `s` has two references and the write copies. Measured: `shared-copies`.
2. **A read result that shares memory.** A reader may return its fraction honestly and keep the value it received; if that value shares mutable structure, the next write copies. Model 5 closes this by construction: reads end only at observation types (`ObsDesc`), which contain no array and no struct of the state.
3. **The library's own temporaries.** The take-out pair is a second reference to the extracted element (§3.4).

### 3.3 A lawful instance can still leak — and lawfulness is about the encoding

`ScidoniaTest/Model5.lean:321` defines `leakyArrayStateVar`, whose `observe () s := s` returns the protected array, with a constructor-faithful injective encoder that emits no `.loc`; all four laws hold (`leakyArray_read_returns_state` at `:335`, `leakyArray_encoding_of_two` at `:341`). The laws therefore constrain the *encoding*, not the object graph; `NoRef` is a statement about the encoding only. The countermodel establishes that for that instance; it is not a claim about all instances.

`SealedStateVar` closes this by construction: an instance supplies a layout and `rep : σ = State layout`, and the library fixes `Result` and `encodeRead` (`rfl`). An `observe` or `encodeRead` field is refused by elaboration, and `SealedStateVar.observe` is not a name a client can write (`ScidoniaTest/Sealed.lean`) — refusals about elaboration, not about runtime counts.

### 3.4 Compiler facts we measured, each of which cost a false claim

| Observation | Evidence (and its kind) |
| --- | --- |
| An array captured by `Task.spawn` is marked thread-shared, `lean_is_exclusive` is false for it thereafter, and the first write after the join copies — **outside this model**: it is a fact about Lean's runtime, recorded because it bounds any future multi-threaded backend, not because this model uses threads | measured (`AGENTS.md:244`) |
| A compiled array *literal* is persistent, never exclusive, so it always copies | measured: `literal-copies` |
| Identical expressions (`Array.replicate n 0` twice) are merged into one shared array | measured in the first in-place probe |
| A projection kept alive across a run makes the write copy | measured; the harness fix is recorded in `ScidoniaInPlace/Main.lean` |
| **Trap 1.** The take-out returns `(array, element)`; while that pair is live the element has two references, so the focus check fired on a unique array | measured: `layout5-checked-unique` failed; after destructuring, the generated C releases the pair before the check (compiler evidence) |
| **Trap 2.** With the update returning `State d × Bool`, reset/reuse fired on the *transient* pair, so the stored struct was a fresh allocation and copied — even though `lean_is_exclusive` + `lean_ctor_set` appear in the C | measured: `layout5-unique` observed a changed address; fixed by the state-only update (`StateVar/Layout5.lean:37`, `:685–716`); compiler evidence corroborates |

Two lessons. Reading the generated C is not evidence about the object that matters, so in-place claims need address assertions. And the update's *shape* decides reuse, so that is an obligation on whoever writes updates, not something the permission discipline supplies.

### 3.5 What sealing closes, stated carefully

For a **safe client, through the exported operations**, the session state and its mutable subtrees are unreachable: the state type is not constructed by the client, the interpreter is private, and reads return only observation values. Under that restriction, "no reader is out" coincides with "no *client* alias" (L3). It does **not** establish L3′: a client can still be in a context where its own earlier values keep an object alive, unsafe or foreign code is outside the guarantee, and the library's own temporaries and the compiler's decisions are untouched by the surface. L3′ remains an invariant to be measured per path, and, at best, proved in a model (§4 S5).

## 4. Proposal: cheapest first

### S1 — Seal the program surface: a session whose state type clients cannot name

Expose a program over a layout, with the state type abstract:

```lean
Program (d : Layout) α          -- pure | get (ObsPath d) k | set (ObsPath d) x k
Reader  (d : Layout) α          -- pure | get … | size … | parallel l r k
runFresh : Init → Program d α → IO α
```

**The export boundary must be specified, not assumed.** Public: the layout and observation codes and their interpretations as *types*; typed paths; the builders `pure`/`bind`/`get`/`size`/`set`/`parallel`; `readPhase`; `runFresh`; and the observation encoding, for display. **Not public**, and each pinned by a refused probe from an external module: the state type's constructor or any function `State d → …`; the interpreters; any operation returning the state or a mutable subtree; the one-hole contexts and take-out primitives.

Two things must be decided explicitly rather than left to the reader:

- **Arbitrary result type `α` and continuations.** A client's continuation may compute any *pure* value from observations, including a closure over an observation; the claim is that no operation can hand it the state, so such a result cannot capture it. This is the same restriction Model 1 already carries, and its limits are the same: it does not constrain what a continuation computes, only what it can be given.
- **An exported evaluator.** If any evaluator over the trees were public, a client could run a program against *its own* state; harmless for the session, but it would mean the state type is nameable, so S1 as specified keeps the interpreters private.

Excluded from the guarantee: `unsafe`, `@[extern]` code, and anything the runtime does with values the client obtained outside the API.

- **Buys:** removes routes 1 and 2 of §3.2 by construction, and makes the surface's claim testable by probes. It is API-level escape control, not a proof of L3′.
- **Cost:** a new surface and interpreter, plus probe tests for every excluded route; and the interpreter is new code that must keep the L3′ discipline (S2).
- **Consequence for the pitch:** with the state unreachable, the fractions are no longer what gives write exclusivity — the type structure does (`Reader` has no write; a write exists only outside a read phase). The fractions remain the *sharing* accounting: how a fork splits authority, why a join waits for every branch, and why every interleaving agrees.

### S2 — Library-side obligations, asserted per supported shape

Obligations attach to **the executor's write paths, the primitives (`swapAt`/`plugAt`/`set!`) and each supported mutable nesting and update form** — not to hypothetical user instances, of which the closed universe has none. Each must: destructure the take-out pair before any check; thread the focus as a value, never as a closure over the old state; return the state alone so a struct cell can be rewritten; and avoid holding a projection across the recursion.

- **Buys:** makes S1's non-escape claim about *code* rather than intent, for the shapes covered.
- **Cost:** discipline in the interpreter, and a harness case per supported shape, with address assertions on the root **and** on each mutable focus (the `layout5-nest*` cases do this for a nested array).
- **Caveat on the instrument:** checked mode (`SCIDONIA_CHECK_INPLACE=1`) is *diagnostic*. In an unchecked run it neither enforces nor reports; and the check itself depends on the runtime's exclusivity primitive, which is part of the trusted base.

### S3 — A deep uniqueness check in checked mode

Extend the check from the top-level object to the layout's mutable footprint, requiring count 1 at every mutable node before a write.

- **Buys:** catches nested sharing that a root-only test cannot see; independent of the instance author.
- **Cost:** O(footprint) per check, and false alarms where immutable parts are deliberately shared. Diagnostic, as S2.

### S4 — Check the compiled code at definition time

Lean's IR, after reference counting is inserted, is available during elaboration (`IR.findEnvDecl`). An attribute could run a small alias analysis over the executor's generated code and refuse code that (a) increments the state into a result, or (b) passes a still-referenced cell into an in-place mutation — the two traps of §3.4, caught mechanically.

- **Buys:** covers what the compiler actually emits, including shapes a human will not re-read.
- **Cost:** a checker to maintain against Lean's IR; checking, not proof.

### S5 — Prove uniqueness in a counted model

Model the heap with reference counts (λRC, from Ullrich and de Moura, *Counting Immutable Beans*), state the sealing assumptions as hypotheses — the object never escapes, every read result is built from the observation universe — and prove: authority 1 at a write implies count 1 for the modeled object.

**This is a theorem about the model, and must be described as one.** To infer a property of compiled executions, the following correspondence chain is needed, and each link is either verified or trusted:

1. the model's allocation, aliasing and count transitions correspond to Lean's object allocation and count operations;
2. the primitives (`swapAt`, `plugAt`, `set!`, the exclusivity test) implement their stated contracts;
3. the compiler's IR transformations — including reset/reuse — and code generation preserve the modelled condition;
4. the runtime executes the emitted code faithfully.

A verified-translation path (1–3 as proofs) and a trusted-correspondence path (the same links assumed and stated) are different results and must be labelled differently.

- **Buys:** turns L3′ for a class of programs from "measured" into "proved in a model", with assumptions explicit.
- **Cost:** research-scale, plus whichever links remain trusted.

### What cannot be done in Lean

Lean's ordinary value and type system does not prevent copying a value, and it has no affine or uniqueness typing of the kind Rust's borrows, Clean's uniqueness types or Linear Haskell provide. Therefore general, source-level uniqueness (L3′ for arbitrary values and code) is not enforceable in Lean by types. That is a property of the host language, and it does **not** mean no ownership discipline is expressible: API-level capability and escape control — private constructors, sealed interpreters, continuation-scoped operations — can enforce a narrower discipline, which is exactly what S1 does, and what Model 1 already does.

### Alternatives considered, and their costs

| Option | What it gives | What it costs / does not give |
| --- | --- | --- |
| Effect structure / `Std.Do` | explicit, composable stateful operations and capabilities to structure an API | do-notation, monads and handlers do not restrict copying ordinary values: an organisation option, not uniqueness typing |
| Runtime ownership hints: borrowed `@&` parameters, mark/linearisation primitives | may inform whether the compiler treats a value as uniquely owned or borrowed, and can reduce copies | not a source-level affine discipline; correct use is a compiler/runtime contract, needs per-toolchain experiments and expands the trusted runtime boundary |
| Opaque foreign-owned state (a C/Rust owner behind a narrow FFI) | Rust can enforce ownership internally while Lean sees only an abstract capability, so clients cannot alias the store | FFI, handle lifetime and resource management, error and concurrency semantics, build integration, and a trusted native code base and ABI — it narrows the boundary rather than proving uniqueness |
| Capability/session handle (S1 sharpened) | a private session object with operations scoped to one runner states non-escape more clearly than an unnamed state type | still API-level escape control; requires the same proof obligation that every constructor, result, continuation and exported evaluator preserves the boundary |

None of these replaces S1 + S2; each narrows the contract in a different place, and the last is a refinement of S1 rather than an alternative to it.

## 5. Recommended order

1. **S1 + S2** as one milestone: S1's claim rests on the interpreter keeping one reference, and S2 is what makes that true and checked. This is the step that makes non-escape true for client code.
2. **S4** next: the cheapest mechanical protection against the two traps, covering code no human will re-read.
3. **S3**, where a layout is available, for nested footprints.
4. **S5** as the research goal, with its correspondence chain stated up front.

## 6. Evidence each step should add

| Step | Acceptance evidence | Claim it would support |
| --- | --- | --- |
| S1 | refused probes for every raw-state route named in the export boundary, from an external module; positive checks for the supported operations | structural: the surface's shape (no claim about counts) |
| S2 | named harness cases with address assertions for each supported shape: root and each mutable focus, unique and aliased; the aliased case aborts under checked mode | measured: L3′/L4 on those paths, with checked mode named as the instrument |
| S3 | a case with a deliberately aliased nested element: unique passes, aliased aborts naming the nested site | measured: footprint-wide, checked mode only |
| S4 | the checker rejects a deliberately bad instance (a retained closure, an un-destructured pair) and accepts the shipped ones | checked: the emitted code's shape |
| S5 | the model theorem with its hypotheses listed, and an explicit list of which correspondence links are verified and which are trusted | proved in the model; not a claim about compiled executions |

## 7. Open questions

1. Is S1's strictness worth making `State` unnameable, given it also removes running the operations on one's own value?
2. Should the ledger's role be stated plainly as *sharing* accounting (parallel safety), with non-escape owned by sealing? That is a change in the pitch, not in the code.
3. For S4, is a checker over Lean's IR acceptable to maintain, or is that effort better spent on S5's model?
4. For S5, is "proved in the model, correspondence trusted and stated" the honest and sufficient result to publish, or is the verified-translation path required?

## 8. Non-claims

- No theorem here certifies in-place update for compiled code, and none certifies anything about Lean's object graph.
- `NoRef` is about the modelled encoding; `SealedStateVar` removes the author's choice of that encoding but does not prove the library's encoding matches runtime references.
- Sealing establishes non-escape through the exported operations, under the exclusions of S1. It does not establish L3′.
- Checked mode is diagnostic: it neither proves nor enforces in runs where it is disabled.
- Copying in Lean is always safe: a missed in-place update costs time, never correctness or a race.
- Every measured claim in this document is measured on this toolchain, on the named harness cases.
- The fork/join is notional; the executor is sequential, and a real concurrent backend would still face the thread-shared marking of `Task.spawn`.

## 9. Pointers

- `AGENTS.md:228, 244, 332, 456, 466, 559` — what is proved, and what is only runtime evidence.
- `Scidonia/FracPerm/StateVar/Layout5.lean:37, 46, 57, 60, 63, 685–716` — the take-out, the checks, the update shape.
- `Scidonia/FracPerm/StateVar/Sealed.lean` — the sealed class, its derived laws and instances.
- `ScidoniaTest/Model5.lean:321, 335, 341` — the leaking lawful instance and the refused raw-state routes.
- `ScidoniaTest/Sealed.lean` — the refusals that make the sealed surface structural.
- `ScidoniaInPlace/Main.lean` — the harness cases and their address assertions.
