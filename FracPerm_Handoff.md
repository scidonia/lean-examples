# Fractional permissions in Lean 4 — handoff for discussion

Repository: `Scidonia/lean` (branch `master`, commits `ed0c9a8`, `fc37899`, `a6c2945`).
Toolchain: Lean `4.35.0-rc3` from a Nix flake (`nix develop -c …`, or direnv `use flake`). No Mathlib; only core Lean plus the `std` package.

## 1. What exists

A library, `Scidonia.FracPerm`. Programs over a state value `σ` (an `Array`, or any user object) can only be run through a **Hoare monad** that tracks **fractional read permissions** in a **ghost ledger**:

- `write` needs the whole permission (`held = 1`).
- Any number of reads may be out at once. Each takes a fraction `0 < q ≤ held`.
- Returning a read gives back exactly its fraction. `exec` only runs a program if the caller proves that every fraction taken out was returned exactly once.
- All of this is checked statically, as proof obligations in the program's type. The ledger and every proof are erased at compile time.

Separately, a **runtime in-place check** (`SCIDONIA_CHECK_INPLACE=1`) asserts, at each write, that the state is exclusively owned. That is the condition for Lean's runtime to update it in place rather than copy it. A harness executable asserts which usage patterns are in place and which copy.

### Files

| Path | Content |
|---|---|
| `Scidonia/FracPerm/Ledger.lean` | `Ledger := List (Nat × Rat)`, `held l = 1 - Σ fractions`, theorems `held_nil`, `held_cons`, `held_erase_of_mem` (a return adds back exactly `q`) |
| `Scidonia/FracPerm/Hoare.lean` | `FracObject` class, `Array` instance, `ReadTok`, `HSt` monad, `ret`/`bind`/`conseq`/`>>>=`, `acquire`/`read`/`release`/`write`/`withRead`/`exec`, tactic `hst_vc` |
| `Scidonia/FracPerm/InPlace.lean` | `assertExclusive` (identity in the logic, exclusivity check when compiled), the env switch, the abort |
| `Scidonia/FracPerm/Counter.lean` | Second instance: `structure Counter { hits : Nat, log : Array Nat }` |
| `ScidoniaTest/FracPerm.lean` | Compile-time checks: accepted programs with `#guard`; each rejected program has a theorem that its obligation is **false** |
| `ScidoniaExamples/Linearity.lean` | Tutorial: accepted programs, rejected programs with the error the user sees plus a falsity theorem, and stated limits |
| `ScidoniaInPlace/Main.lean` | `lake exe inplace`: a runtime harness asserting in-place updates or copies, with controls |
| `AGENTS.md` | Build commands, erasure facts, how to write an instance, how to read the generated C |

### Commands

```
nix develop -c lake build                    # library
nix develop -c lake build ScidoniaTest       # compile-time checks
nix develop -c lake build ScidoniaExamples   # tutorial
nix develop -c lake exe inplace              # in-place harness (12 cases, exit 0)
SCIDONIA_CHECK_INPLACE=1 .lake/build/bin/inplace shared   # expected: exit 1 + diagnostic
```

## 2. Core design

```lean
abbrev Ledger := List (Nat × Rat)              -- outstanding reads: (ghost id, fraction)
def Ledger.held (l : Ledger) : Rat := 1 - (l.map Prod.snd).sum

class FracObject (σ : Type) (ReadOp : outParam Type) (WriteOp : outParam Type) where
  Result   : ReadOp → Type
  observe  : (o : ReadOp) → σ → Result o
  update   : WriteOp → σ → σ
  check    : String → WriteOp → σ → σ := fun site _ s => assertExclusive site s
  check_eq : ∀ site o s, check site o s = s     -- identity in the logic

structure ReadTok (n : Nat) (q : Rat) : Type where private mk ::   -- no fields

abbrev Pre  σ   := Ledger → σ → Prop
abbrev Post σ β := Ledger → σ → β → Ledger → σ → Prop

structure HSt (σ) (P : Pre σ) (β) (Q : Post σ β) where
  private mk ::
  private run : Cap → (s : σ) → (∃ l, P l s) → { r : β × σ // ∀ l, P l s → ∃ l', Q l s r.1 l' r.2 }
```

- **Hoare monad, Swierstra style.** The precondition is a predicate on (ledger, state). The postcondition relates the pre-state, the result and the post-state. `bind` composes them as weakest-precondition-style conjunctions and existentials. `conseq` weakens a specification.
- **Primitive specs:**
  - `acquire n q`: pre `n ∉ ids ∧ 0 < q ∧ q ≤ held`; post `l' = (n,q) :: l`; returns `ReadTok n q`.
  - `read t o`: pre `(n,q) ∈ l`; post: unchanged, and the result is `observe o s`.
  - `release t`: pre `(n,q) ∈ l`; post `l' = l.erase (n,q)`.
  - `write o`: pre `held = 1`; post `s' = update o s`.
  - `withRead n q body` = acquire ▸ body ▸ release ▸ ret. It is derived from the other primitives, so it adds no trust.
  - `exec m s (hp : P [] s) (hq : ∀ b l' s', Q [] s b l' s' → l'.held = 1)`.
- **Ghost ids are chosen by the caller.** There is no runtime counter, because the ledger does not exist at runtime.
- **Fractions are core `Rat`.** Plain `decide` gets stuck on `Rat`. `decide +kernel` and `grind` both work, including for symbolic goals, so `hst_vc` is `simp [Ledger.held] at * <;> grind`.

### Sealing: how "only usable through the permission type" is enforced
- `HSt.mk` is private, so programs cannot be forged.
- `run` is private. That alone was not enough: Lean's auto-generated `HSt.casesOn` and `HSt.rec` still exposed it. So `run` also demands `Cap`, a `private structure Cap : Prop` that only the module can construct. A client cannot reach `run` through either route; both rejections are pinned by `#guard_msgs` checks.
- `ReadTok.mk` is private, so tokens cannot be forged.
- **Remaining escapes:** `unsafeCast` and other `unsafe`/`implemented_by` code can bypass everything. That is out of scope; it breaks all of Lean's guarantees.

### What "linear" means here
- Lean values can be copied, so this is **not** linearity of token values.
- It is linearity of **ledger entries**: every fraction taken out must be returned exactly once before `exec` accepts the program. Never returning one (`exec`'s closing condition) and returning it twice (`release`'s precondition) are both rejected.
- A token is a **name** for an entry. A copied token is not a second permission, and once the entry is gone every copy is dead.
- Tokens with the same `(n, q)` share a type and carry no data, so they are interchangeable. After an id is returned and re-acquired, an old copy names the new entry (example L1). The accounting stays exact.

## 3. Erasure: what exists at runtime (observed in Lean IR and the generated C)

| Thing | Runtime representation |
|---|---|
| Ledger, all pre/post conditions, all proofs, `Cap` | erased (`◾`) |
| `ReadTok n q` value | a constant scalar `ctor_0`, the same as `Unit`: no allocation, no reference counting |
| `n : Nat`, `q : Rat` passed with literal values | removed by arity reduction (`acquire._redArg`) |
| `n`, `q` computed by a caller (e.g. `k*7`, `r/2`) | **not evaluated**: the call goes through `_redArg` and the argument code is removed as dead |
| `n`, `q` in a definition generic over them | they stay in that definition's public signature as unused borrowed (`@&`) parameters |
| `n`, `q` through a function value (closure / `_boxed`) | computed and boxed (a real cost, e.g. a `Rat.div` allocation) |

Lean erases arguments **by their type** (proofs, types, type formers), not by whether they are used. A `Ghost α := α → Prop` wrapper would erase completely (prototyped; IR shows `◾`). A singleton-structure `Ghost` compiles to a tagged scalar. We chose plain `Nat`/`Rat` and documented the limit.

## 4. In-place update: findings (all observed by running compiled code)

**How it is measured.** `isExclusiveUnsafe` before the program runs, and `ptrAddrUnsafe` before and after. A copy always allocates a new object, so the same address means the update happened in place.

| Situation | Result |
|---|---|
| A uniquely owned array run through write/acquire/read/release/write | in place |
| The array still referenced elsewhere (a control) | copied; the original is unchanged |
| A literal `#[0,0,0,0]` | always copied: compiled literals are static constants, never exclusive |
| A "fresh" `Array.replicate n 0` next to a second identical expression | **copied**: the compiler merged the two identical expressions into one shared array and emitted `lean_inc_ref` |
| A harness reading `s.log`'s address before running the program | **copied**: the compiler kept the `s.log` projection alive across the run |
| A structure `{ s with hits := …, log := s.log.push x }` on an exclusive `s` | struct and `log` both in place (reset/reuse) |
| The same, but also returning `s.log.size` from the old `s` | struct reused, **`log` copied** |
| `Array P` of structs updated with `ps.modify i f` | array in place, nested `tags` in place, struct header reallocated (only its fields moved) |
| `Array P` updated with `let p := ps[i]!; ps.set! i {p with …}` | array in place, **struct and nested `tags` copied** |

**What the library code itself does (generated C, `.lake/build/ir/Scidonia/FracPerm/*.c`):**
- `write` passes its owned state to `check` and then to `update`/`lean_array_set`.
- `bind` briefly raises the state's reference count while it unpacks the intermediate pair, and freeing the pair brings it back to 1 before the continuation runs.

**The check.** `assertExclusive` is the identity in the logic; it is compiled through `@[implemented_by]` to a `lean_is_exclusive_obj` test. The `SCIDONIA_CHECK_INPLACE` env var is read once at startup. When checking is off, a write costs one out-of-line call, one load and one branch. On failure it prints the site and exits 1, and it still exits 1 if the diagnostic can't be printed.

**A regression we hit.** One version of the abort path made the checker take its state as **borrowed** rather than owned. The compiler then inserted `lean_inc_ref`, and every write silently copied. Only the harness's unique-array cases caught it. Whether a parameter is owned or borrowed is fragile and needs to be tested, not just read off the code.

**Per-operation check.** The `check` hook receives the `WriteOp`, so `Counter` checks `log` only for `record`. A checked-mode abort therefore means "this write is about to copy", not just "some part is shared".

## 5. Known limits

1. **Permissions don't control references.** The ledger exists only in proofs, while copying depends on actual reference counts. Nothing stops a program holding a read result across a write.
2. **Instance authors are trusted.** Only the permission rules hold for arbitrary instances: a hostile instance still cannot cause a write without `held = 1` (`check_eq` keeps the check logically inert). In-place behaviour depends on `observe` and `update`:
   - `observe` must not return a reference to a part of the state that some write updates in place (e.g. returning the `log` array).
   - `update` must not keep old parts alive.
   - Sharing values that are never mutated in place (a big `Nat`) is harmless.
   - These rules are documented, not enforced.
3. **Leaks only cost performance.** Lean is pure, so a leaked alias makes a later write copy. It never produces a wrong result or a race.
4. **Sequential only.** No concurrency.
5. **One object per program.** No `do`-notation; programs are written with `>>>=`.

## 6. Open design questions (no decision yet)

**A. Getting dropped fractions back.**
- Scoped reads (`withRead`) are implemented.
- A `reclaimAll` (revoke every entry) would be **sound in this design**, because a token's power is its ledger entry, and dead copies can't be used. But it would weaken the guarantee from linear to "no read after revoke", and it would be unsound if reads ever became concurrent. Not implemented.

**B. Protection against untrusted instances.**
1. *A sealed list of allowed read result types:* `NoAlias τ` with a private-constructor field, so only the library can add instances (scalars, `Nat`, `Int`, and `Option`/`Prod`/`Sum` of them). This is static, but it restricts what reads can return.
2. *A deep uniqueness walk in checked mode:* check that every heap object reachable from the state has reference count 1, at every read and write. Independent of the author, catches internal sharing, costs O(size), and gives false alarms on deliberate internal sharing of immutable parts.
3. *Safe by construction:* authors describe the object's layout with library combinators (scalar, struct, array of a layout). The library derives path reads that end in safe types and writes that take the element out first (the `Array.modify` pattern). No-leak is then a property of a finite set of combinators. This handles **arrays of structs** naturally.
4. *Checked against compiled code:* the IR is available during elaboration. `IR.findEnvDecl (← getEnv) name` returned the post-reference-counting IR, with `inc`, `isShared` and in-place `set`. An attribute could run an alias analysis on an instance's `observe`/`update` IR and refuse instances that leak. This checks the real compiled code, but it is a checker, not a proof.
5. *Proof by reflection:* reify instance code into a deep embedding, write a decidable no-leak checker, and prove it sound against a formal reference-counting semantics (λRC from "Counting Immutable Beans"). This is a real proof, but only against a model of Lean's compiler, which itself is unverified.

These combine well: (3) for most users, (4) to guard hand-written instances, (5) as the research contribution.

**C. Arrays of structs.** These need path reads (field `f` of element `i`) and take-out writes; see the table in §4. This fits B3.

## 7. Prior art to compare against (for the novelty question)

- **Boyland 2003**, fractional permissions. **Iris**, **VeriFast** and **Viper**: fractional permissions in separation logic.
- **F\* Pulse/Steel**: fractional permissions on arrays as ghost state, extracted to C with real mutation. Likely the closest existing system.
- **Verus (Rust)**: ghost, tracked and executable modes; linear ghost permissions.
- **Swierstra**, "A Hoare logic for the state monad"; **Hoare Type Theory / Ynot** (Nanevski et al.).
- **Ullrich & de Moura, "Counting Immutable Beans"**: Lean's reference counting and reset/reuse, and the λRC semantics.
- **Koka Perceus**, and **"FP²: Fully in-Place Functional Programming"** (Lorenzen, Leijen, Swierstra, ICFP 2023): a static `fip` check, proved sound, that a function runs fully in place. Probably the closest prior art to B4 and B5.
- **Clean** uniqueness types; **Linear Haskell**; Rust borrows. These enforce statically the reference discipline we can only check at runtime.
- **Mathlib** `Erased α`; **Dafny** `ghost`; **F\*** `erased` and the `Ghost` effect.

**Candidate novelty.** These are hypotheses to test, not established:
1. Erased fractional permissions as a sealed Hoare monad in Lean 4 core, with permissions identified only by type indices.
2. A per-operation in-place check that is the identity in the logic but does real work when compiled, plus a harness that validates in-place claims against Lean's reference-counted runtime.
3. Directions B3 to B5: a no-leak law for user instances, enforced by construction, by IR analysis, or by proof against λRC. Linking fractional permissions to FBIP-style in-place guarantees in Lean looks unexplored. Koka's FP² is the comparison point.

## 8. Questions to discuss

1. Is the payoff of permissions in a **sequential pure** setting enough on its own: a protocol discipline plus the conditions for in-place update? Or does the work only become compelling with concurrency (tasks, shared readers), where `reclaimAll` would become unsound?
2. Which no-leak route, B1 to B5, gives the best research-to-engineering ratio? Is proving soundness against λRC feasible inside Lean without Mathlib?
3. Should tokens be indexed by `Ghost` (`α → Prop`) so they erase fully, at the cost of noisier specifications?
4. How do we compare honestly with Pulse and with Koka's FP²? What is a concrete benchmark: an array-of-structs workload, checked for in-place behaviour, with and without the discipline?
5. Do we need `do`-notation for an indexed or Hoare monad to make this usable, and how would it interact with Lean's own program logic, `Std.Do` (`import Std.Do`: `Std.Do.Triple`, `Std.Do.WP`; present in 4.35)?
