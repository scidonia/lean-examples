# Enforcement and run time

## What gets rejected
- Writing while a read is out. Returning a token twice. Reading after returning. Taking out more than is held. Reusing an id. Never returning a read.
- Each is a theorem that the program's obligation is ==false== — not merely that a tactic gave up.

```rejected
import ScidoniaTest.FracPerm
open Scidonia.FracPerm HSt

-- acquire 1/3, then write while it is out
example : n1Prog =
    (acquire (σ := Array Nat) 0 (1 / 3) >>>= fun _ =>
      write (0, 7)) := rfl

example (a : Array Nat) : ¬ HSt.pre n1Prog [] a :=
  n1_write_while_read_outstanding a
```

## Sealing
- `HSt.mk` and `ReadTok.mk` are private: programs and tokens cannot be forged.
- A private `run` field was ==not enough==: Lean's generated `HSt.casesOn` still handed it out.
- So `run` also demands `Cap`, a private `Prop` that no client can construct, and that erases.
- `exec`, from the empty ledger and with the closing proof, is the only entry point.

## What exists at run time
- The ledger, every specification, every proof and `Cap`: erased, `◾` in the IR.
- A `ReadTok n q` has no fields: a constant scalar, like `Unit`.
- `n : Nat` and `q : Rat` are ordinary arguments — Lean erases by *type*, not by use.
- Arity reduction removes them from direct calls, even computed ones such as `r / 2`; only a call through a function value computes them.

## In place means reference count 1
- `lean_array_set` writes in place when the array is exclusive, and copies it otherwise.
- Measured in compiled executables, by exclusivity and pointer identity:
  - a unique array through a program: in place
  - a second live reference: copied
  - an array literal: always copied, it is a static constant
  - two identical `Array.replicate n 0`: ==merged by the compiler==, so copied
  - `{ s with log := s.log.push x }`: in place; also returning `s.log.size`: `log` copied

## A check that is the identity in the logic
- `assertExclusive` is `fun _ s => s` to the kernel, so specifications and proofs never see it.
- `@[implemented_by]` swaps in code that tests `lean_is_exclusive`, and exits when `SCIDONIA_CHECK_INPLACE=1`.
- The generated C runs the test right before `lean_array_set`.
- One version made the check's parameter *borrowed*: the compiler added an increment and every write copied. ==Only the harness caught it.==

```identity in the logic
import Scidonia.FracPerm
open Scidonia.FracPerm

example (s : Array Nat) :
    assertExclusive "site" s = s := rfl
```

## Any object, not only arrays
- `FracObject σ ReadOp WriteOp`: an object names its read operations (`observe`) and write operations (`update`).
- A per-operation `check`, with the law `check site o s = s`, so an instance can check only what that write mutates.
- `Array` and a `Counter` (a count and a log) are instances; the permission rules hold for every instance.

```an instance
import Scidonia.FracPerm
open Scidonia.FracPerm

example : FracObject.update (σ := Counter)
    (Counter.WriteOp.record 3) ⟨0, #[]⟩ = ⟨0, #[3]⟩ := rfl
```

## FracObject: the definition
- Restated here and checked against the library: the panel compiles only if the library's class has these fields at these types.
- `check` defaults to `assertExclusive` on the whole object.
- The rules for `observe` and `update` — no aliases into mutable state — are *not* fields: they are documented, and nothing enforces them.

```class FracObject
import Scidonia.FracPerm
open Scidonia.FracPerm (assertExclusive)

namespace Shown
class FracObject (σ : Type) (ReadOp : outParam Type)
    (WriteOp : outParam Type) where
  Result : ReadOp → Type
  observe : (o : ReadOp) → σ → Result o
  update : WriteOp → σ → σ
  check : String → WriteOp → σ → σ :=
    fun site _ s => assertExclusive site s
  check_eq : ∀ site o s, check site o s = s
end Shown

-- The library's class has exactly these fields.
example [i : Scidonia.FracPerm.FracObject σ R W] :
    Shown.FracObject σ R W := { i with }
```

## Permissions do not control references
- The ledger lives in proofs; copying depends on run-time reference counts.
- An `observe` that returned the `log` array would leave an alias, and the next write would copy.
- A leak only costs speed: Lean is pure, so results stay correct.
- Remedies under discussion: sealed result types, a deep uniqueness walk, safe-by-construction layouts, checking an instance's IR, a proof against λRC.

## Structured: Reader and Program
- A second, smaller interface: clients see no fractions, tokens or ledger.
- `Reader`: `get`, `size`, `parallel`. `Program`: `readPhase`, `set`. Ordinary `do` notation.
- `runFresh` creates the array itself, and ==no public route reaches it==.

```reads in parallel
import Scidonia.FracPerm
open Scidonia.FracPerm.Structured

def example₁ : Program (Option UInt64 × Option UInt64) := do
  let _ ← Program.set 0 17
  let (a, b) ← Program.readPhase
    (Reader.parallel (Reader.get 0) (Reader.get 1))
  let _ ← Program.set 1 23
  return (a, b)

#eval do
  let r ← runFresh { size := 1024, fill := 0 } example₁
  unless r == (some 17, some 0) do
    throw (IO.userError "unexpected result")
```

## Fractions in the semantics
- A fork gives each branch half its parent's share; a join restores it once both branches have finished.
- The executor runs branches one after the other; the semantics allows every interleaving.
- Proved: shares are conserved, no write step exists while readers hold shares, a read phase ends only fully joined, results depend only on what was observed, and ==every interleaving yields the executor's result==.

```every interleaving agrees
import Scidonia.FracPerm
open Scidonia.FracPerm.Structured

example {s : Array UInt64} {t : RTree α} {a : α}
    (h : StepStar s (.run 1 t) (.run 1 (.pure a))) :
    a = val s t :=
  complete_run_value h

example {q : Rat} {t : Thread α} (h : WF q t) :
    leafSum t = q :=
  wf_leafSum h
```

## Why the fork/join is notional
- An array captured by `Task.spawn` is marked as shared between threads.
- `lean_is_exclusive` is false for such an object for good, even after every task has finished.
- Measured: the first write after a real parallel read phase copies the whole array.
- A concurrent backend needs support from the runtime, not only permissions.

## Related work
- Fractional permissions: Boyland; Iris, VeriFast, Viper.
- F* Pulse and Steel: fractional permissions on arrays, extracted to C.
- Koka's FP² (Lorenzen, Leijen, Swierstra, 2023): a checked fully-in-place discipline.
- Lean's reference counting: Ullrich and de Moura, *Counting Immutable Beans*.
- Hoare state monads (Swierstra); Hoare Type Theory.

## Open questions
- Which route to no leaks: by construction, by checking instance IR, or by a proof against λRC?
- Arrays of structs: path reads and take-out writes.
- A concurrent backend that restores exclusivity after a join.
- Is the sequential discipline worth having on its own?
