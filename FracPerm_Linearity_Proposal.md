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

**Proved.** The permission protocol (a write needs `held = 1`; a read needs its ledger entry; every fraction returned exactly once); share conservation, exclusion, joins, schedule independence and replay over the structured semantics; detached reads *in the modelled encoding* (`NoRef`); snapshots and frames; `setLeaf` equals the zipper's path replacement. In the layout universe, `encodeObs` is injective and location-free for every observation description, and a whole-array read has no `ObsPath`. In the counted presentation (`StateVar/Footprint.lean`), the count of a reference is defined from aliasing rather than assumed; the facts the write test rests on follow from that definition — one handle to a reference no slot names is one live reference, the take-out pair's two handles are two, two slot occurrences naming one cell are at least two, and a one-cell write moves a count by exactly the changed cell's contribution — and the layer composes with `observe_detached` through `read_at_detached`, so a run whose issued read results are detached holds no handle on the root but the runner's own and the root's count is one. The presentation reading and the runtime agreement (`RuntimeAgrees`) are hypotheses, not theorems, and the module says so; relating the presentation to a layout's `State d` is not done.

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

### 3.6 When we get update semantics: the shape rules

A mutation site asks one question: is this object's count exactly 1 here? Count 1 → update in place; otherwise → allocate a copy. Twelve minimal cases, each compiled and run on this toolchain (address measured before and after; a scratch executable, not yet part of the harness):

| Case | Code | Address kept? |
| --- | --- | --- |
| A | `a.set! i v` on an owned array | in place |
| A′ | the same, with a live alias to `a` | copied |
| B | `(a.set! i v, a.size)` — no alias, one extra use | copied |
| C | `{ s with hits := s.hits + 1 }` | struct cell reused |
| D | `({ s with log := s.log.set! 0 v }, s.log.size)` | struct reused, `log` copied |
| E | `({ s with hits := s.hits + 1 }, true)` | struct cell reused |
| F | `{ s with log := s.log.set! 0 v }` | `log` in place |
| G | `a.modify i (fun inner => inner.set! j v)` | inner in place |
| H | `let inner := a[i]!; a.set! i (inner.set! j v)` | inner copied |
| I | `fC s` with an alias to `s` live | copied |
| J | `a.push v` with room to spare | in place |
| J′ | `a.push v` with no room | reallocated |
| K | `#[0,0,0,0].set! i v` — a compile-time constant | copied (never exclusive) |

Three signals in the emitted IR decide every case: `inc x` before a mutation (the value is used again in the same expression, as in B, or an alias is live, as in A′ and I); `isShared` before a rebuild (the reset/reuse pass rewrites the *incoming* cell when it is exclusive, as in C, D, E, F, G); and take-out versus a borrowed get (`Array.getInternal` + a placeholder `Array.set` in G, against `Array.get!InternalBorrowed` + `inc` in H).

**The rules.**

1. **The object was allocated at run time.** A compile-time constant has count 0 (persistent) and is never exclusive (K) — the reason `runFresh` builds the state at run time.
2. **Its count is 1 at the mutation:** no alias live across the call (A′, I), no projection of it taken and used (H, D), and no second use of the same value in the same expression (B).
3. **A whole-value rebuild recycles the incoming cell when it is exclusive** (C, D, E, F, G), but the pass matches on *shape*: with more than one same-shaped constructor in the expression the cell can go to the wrong one — Trap 2, where the `(state, Bool)` pair was a second `Prod`.
4. **A write nested inside a structure needs every node on the path to be exclusive at the moment of the write.** Take-out makes the node owned (G); a borrowed get does not (H).
5. **The write is a fixed-size element write.** `Array.set!` cannot grow; an append needs spare capacity (J against J′).

**This is not the shape a normal update takes.** A normal update is "check, then write", and the check's result is a scalar, so the state's uses are sequential and the last one is a move: `setLeaf` compiles to `inBounds(path, s)` and then `setAt(path, x, s)` with **no increment of the state at all**. Case B copies because the *new array* had to be used as well; a command surface cannot express that, because the client has no value to write and read at once.

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

**What is in place.** `StateVar/Footprint.lean` defines the count from aliasing over a presentation of the heap and proves the facts the write test rests on — one handle to an unnamed root is one reference, the take-out pair's two handles are two, two slot occurrences are at least two, a one-cell write moves a count by exactly the changed cell's contribution — and composes the layer with the interface's proved detachment (`observe_detached` through `read_at_detached`), so a run whose issued read results are detached holds no handle on the root but the runner's own and the root's count is one. It is **not** the counted-heap model this step names: there is no allocation, no λRC heap and no count transition, and the two hypotheses it rests on — that the presentation is the live heap, and `RuntimeAgrees` — are stated rather than proved, with no instance of `RuntimeAgrees` constructed anywhere. Relating the presentation to a layout's `State d`, so that the schema's `setLeaf` and take-out carry count theorems, is the next step; the correspondence links 1–4 above are untouched. `ScidoniaTest/Footprint.lean` is its check layer.

### S6 — Freeze the update as a schema over the universe (Model 6)

S2's obligations are hand-written in one interpreter, so a later edit can lose them — that is how Trap 2 arose. The remedy is to treat the update as a *schema over the description universe* rather than a per-interpreter habit, and to state its shape obligations explicitly.

The schema is nearly in place already. `setAt` is one structural recursion over `Layout`, a clause per constructor: at a leaf it replaces the focus; at a struct it destructures the cell and rebuilds it from the updated component, returning the state alone; at an array it takes the element out, checks the extracted focus, recurses and puts it back. Two surface restrictions are what make the losing shapes inexpressible, and both hold:

- the update operand's type is an **observation** (`ObsEl p.obs`), so no client value — and therefore no client alias — can be installed;
- there is **no growth operation**: the surface offers fixed-size element replacement only (§3.6 rules 1 and 5).

What remains to be done, and what each part is worth:

- **State the shape obligations** as obligations of the schema: one write per mutable node, on an owned focus; a state-only return from the recursion; no projection or closure retained across the write; take-out before any check at an array.
- **Separate what is provable about the source from what is not.** That the recursion writes exactly one leaf per path is the existing `setAt_spec` — the schema *is* the zipper's path replacement — and that it returns the state alone is a type fact. That the cell the pass reuses is the cell that gets stored is **not a source property**: it is the compiler's choice among same-shaped candidates, which is why S4 checks it and S5 models it.
- **Extension rule:** a new layout constructor, primitive or update form adds its schema clause, its obligation and its harness case, so coverage is a rule of the design rather than an afterthought.
- **Companion:** S4. Together they say "the shape is right by construction" (S6) and "the shape survived the compiler" (S4).

- **Buys:** the shapes that lose in-place become unwritable where types can say so (no client value in, no growth) and stated obligations elsewhere, and the compiler's freedom narrows to reusing the single candidate per mutable node.
- **Cost:** the obligations are documentation plus harness cases until S4 turns them into a check, and each new mutable shape is a new obligation.

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
2. **S6 + S4** as the next pair: S6 makes the shape a schema with stated obligations and an extension rule, and S4 checks the part of it that is the compiler's choice rather than the source's. S6 alone would leave the cell-reuse question to measurement; S4 alone would check a shape nobody had frozen.
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
| S6 | the schema and its obligations written down; refused probes for the surface restrictions (an observation-typed update operand, no growth operation); a harness case per mutable shape, each asserting addresses on the root and the focused cell | structural where types say so; measured per shape; the obligations themselves are stated, and become checked under S4 |

## 7. Open questions

1. Is S1's strictness worth making `State` unnameable, given it also removes running the operations on one's own value?
2. Should the ledger's role be stated plainly as *sharing* accounting (parallel safety), with non-escape owned by sealing? That is a change in the pitch, not in the code.
3. For S4, is a checker over Lean's IR acceptable to maintain, or is that effort better spent on S5's model?
4. For S5, is "proved in the model, correspondence trusted and stated" the honest and sufficient result to publish, or is the verified-translation path required?
5. For S6, does a single generic recursion over the universe plus stated obligations suffice, or does the shape need to be *generated* (a metaprogramming schema) so that the losing shapes are inexpressible rather than documented? The difference is where the obligation lives: in a comment and a harness case, or in a generator that cannot emit the wrong shape.

## 8. Non-claims

- No theorem here certifies in-place update for compiled code, and none certifies anything about Lean's object graph.
- The counted presentation (`StateVar/Footprint.lean`) does not change that. Its count is defined over a presentation of the heap, not over a machine; its two readings — that the presentation is the live heap, and `RuntimeAgrees` — are hypotheses rather than theorems, and no instance of `RuntimeAgrees` is constructed. The layout bridge that would relate the presentation to `State` and give the schema's `setLeaf` and take-out count theorems is not built, and the correspondence links of §4 S5 stay outside it.
- `NoRef` is about the modelled encoding; `SealedStateVar` removes the author's choice of that encoding but does not prove the library's encoding matches runtime references.
- Sealing establishes non-escape through the exported operations, under the exclusions of S1. It does not establish L3′.
- Checked mode is diagnostic: it neither proves nor enforces in runs where it is disabled.
- Copying in Lean is always safe: a missed in-place update costs time, never correctness or a race.
- Every measured claim in this document is measured on this toolchain, on the named harness cases — **except the table in §3.6**, which was measured in a scratch executable (cases A–K) and is not yet part of the checked harness; making it so is part of S6's acceptance evidence.
- The compiler behaviour in §3.6 is a description of this toolchain's emitted code, not a specification: nothing here promises the same shapes behave the same way on another Lean version.
- The fork/join is notional; the executor is sequential, and a real concurrent backend would still face the thread-shared marking of `Task.spawn`.

## 9. Pointers

- `AGENTS.md:228, 244, 332, 456, 466, 559` — what is proved, and what is only runtime evidence.
- `Scidonia/FracPerm/StateVar/Layout5.lean:37, 46, 57, 60, 63, 685–716` — the take-out, the checks, the update shape.
- `Scidonia/FracPerm/StateVar/Sealed.lean` — the sealed class, its derived laws and instances.
- `ScidoniaTest/Model5.lean:321, 335, 341` — the leaking lawful instance and the refused raw-state routes.
- `ScidoniaTest/Sealed.lean` — the refusals that make the sealed surface structural.
- `ScidoniaInPlace/Main.lean` — the harness cases and their address assertions.
