# What it means to be lawful

## Valid: the invariant a state variable promises
- `Valid : σ → Prop` names the states the variable may ever be in: a buffer of exactly four words, a sorted list, a balanced tree.
- The laws are stated *under* `Valid`. Reads must be detached on valid states, not on states that can never arise.
- Being lawful is four proof obligations. Each one closes a specific hole in the generic theory:
  - `initial_valid`: sessions start inside the invariant.
  - `replace_valid`: writes never leave it.
  - `encodeRead_injective`: the encoding cannot hide what a read returned.
  - `observe_detached`: no read result names protected state.

## Law 1 — every session starts valid
- `initial_valid : ∀ i, Valid (initial i)`.
- The generic theorems assume a well-formed configuration, and that includes `Valid s`. A fresh session satisfies it only if `initial` lands inside the invariant.
- To establish it, compute the shape of the initial state and check it against `Valid`.
- It fails for an initializer that builds a buffer of the wrong capacity.

```law 1
def BufValid (a : Array UInt64) : Prop := a.size = 4

-- the initializer the instance uses
example (v : UInt64) : BufValid (Array.replicate 4 v) := by
  simp [BufValid]

-- an initializer of the wrong capacity breaks the law
example : ¬ BufValid (Array.replicate 5 (0 : UInt64)) := by
  simp [BufValid]
```

## Law 2 — writes keep the invariant
- `replace_valid : ∀ w s, Valid s → Valid (replace w s).1`.
- With Law 1 this is an induction: every reachable state is valid. `pstep_wf` uses it at each write step, and `write_at_valid` at each heap write.
- To establish it, take cases on what the write does: an in-bounds `set!` keeps the size, and an out-of-bounds write returns the state unchanged.
- It fails for a write that appends, which grows the buffer past four.

```law 2
def BufValid (a : Array UInt64) : Prop := a.size = 4

def setIn (w : Nat × UInt64) (a : Array UInt64) : Array UInt64 :=
  if w.1 < a.size then a.set! w.1 w.2 else a

example (w : Nat × UInt64) (a : Array UInt64) (h : BufValid a) :
    BufValid (setIn w a) := by
  unfold BufValid setIn at *
  split <;> simp [h]

-- appending is not a lawful write for this invariant
example : ¬ ∀ a : Array UInt64, BufValid a → BufValid (a.push 0) := by
  intro h
  have := h (Array.replicate 4 0) (by simp [BufValid])
  simp [BufValid] at this
```

## Law 3 — the encoding must not forget
- `encodeRead_injective : encodeRead o x = encodeRead o y → x = y`.
- `encodeRead` translates a read result into `Value`, the language in which references are visible.
- Without this law, encoding every result as `.unit` would satisfy Law 4 trivially and say nothing.
- No generic theorem uses it directly. It is there to keep Law 4 meaningful, though not completely: an injective encoding can still misdescribe a result (see Model 5).
- To establish it, take cases on the operation, then on both results; the constructors of `Value` are injective.

```law 3
import ScidoniaTest.StateVar
open Scidonia.FracPerm.StateVar

-- a constant encoding is trivially reference-free ...
example (ℓ : Loc) : NoRef ℓ Value.unit := trivial

-- ... and is exactly what injectivity rules out
example : ¬ (∀ x y : Bool,
    (Value.unit : Value) = Value.unit → x = y) :=
  ScidoniaTest.StateVar.bad_encode_rejected
```

## Law 4 — reads name no protected location
- `observe_detached : ∀ ℓ o s, Valid s → NoRef ℓ (encodeRead o (observe o s))`.
- On a valid state, the encoded result contains no `.loc ℓ` for any `ℓ`, however deeply nested.
- `primitive_detached`, `read_at_detached` and `safe_result` all rest on it.
- To establish it, take cases on the operation. Each result encodes only through constructors that are not `.loc`.
- It fails for a read that returns a location.

```law 4
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar

variable {σ I R W : Type} [inst : LawfulStateVar σ I R W]

-- what the law gives every lawful instance
example {s : σ} {ℓ : Loc} {o : R} (hs : inst.Valid s) :
    NoRef ℓ (inst.encodeRead o (inst.observe o s)) :=
  primitive_detached hs

-- a read returning a location cannot satisfy it
example : ¬ NoRef 0 (Value.loc 0) := not_noRef_loc_self 0
```

## What lawfulness buys
- Laws 1 and 2: every configuration reachable from a fresh session holds a valid state (`pstep_wf`), and so does every heap cell after a write (`write_at_valid`).
- Law 4: every primitive read and every heap read is detached, and a client's result is safe whenever its continuations are (`safe_result`).
- The protocol needs no law at all: share conservation, exclusion, joins and schedule independence hold for every instance.
- What lawfulness does not buy is physical identity: an encoding can describe an alias as a value. That is the hole Model 5 closes.

## Establishing it: a worked buffer
- A fixed-capacity buffer of four words, with a real invariant, so each law has content.
- Reads are `get i` and `size`; a write replaces one in-bounds word.
- The next slides prove each law step by step, then assemble the instance.

```the buffer
inductive BufRead where
  | get (i : Nat)
  | size

abbrev BufResult : BufRead → Type
  | .get _ => Option UInt64
  | .size => Nat

def bufReplace (w : Nat × UInt64) (a : Array UInt64) :
    Array UInt64 × Bool :=
  if w.1 < a.size then (a.set! w.1 w.2, true) else (a, false)

def BufValid (a : Array UInt64) : Prop := a.size = 4
```
