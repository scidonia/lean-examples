# Four models of a state variable

## From one array to any datatype
- Model 1: the structured interface — `Reader` and `Program` over one `UInt64` array.
- Model 2: what a type must ==prove== to be a legitimate state variable.
- Model 3: one datatype, `Slot`, made lawful through a *description* of it.
- Model 4: the laws proved once for ==every== description; `Slot` follows by transport.
- Each model keeps the theorems of the one before, made more general.

## Model 1: the structured interface
- Clients see `Reader` (`get`, `size`, `parallel`) and `Program` (`readPhase`, `set`) — no fractions, no tokens.
- Fork halves a share, join restores it; every interleaving yields the sequential executor's result.
- But the object is fixed: one `UInt64` array, with its operations sealed inside the library.

```one array
import Scidonia.FracPerm
open Scidonia.FracPerm.Structured

example : Nat → Reader (Option UInt64) := Reader.get
example : Nat → UInt64 → Program Bool := Program.set
example {α : Type} : Init → Program α → IO α := runFresh
```

## Model 2: what must a state variable prove?
- `FracObject` *documented* its rules: reads must not return the mutable state. Nothing checked them.
- To state the rule we need a language in which a reference can appear: `Value`, with a constructor `.loc ℓ`.
- `NoRef ℓ v`: no `.loc ℓ` anywhere inside `v`, however deeply nested.

```references, made visible
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar

example : NoRef 0 (.pair (.nat 7) (.some (.uint 3))) := by
  simp [NoRef]

example : ¬ NoRef 0 (.pair (.nat 7) (.some (.loc 0))) := by
  simp [NoRef]
```

## LawfulStateVar: the definition
- Restated here and checked against the library: the panel compiles only if the library's class has these fields at these types.
- Six operations and four laws. The laws are what `FracObject` only documented.

```class LawfulStateVar
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar (Value Loc NoRef LawfulStateVar)
class Shown (σ : Type) (Init : outParam Type)
    (ReadOp : outParam Type) (WriteOp : outParam Type) where
  Result : ReadOp → Type
  initial : Init → σ
  Valid : σ → Prop
  observe : (o : ReadOp) → σ → Result o
  replace : WriteOp → σ → σ × Bool
  encodeRead : (o : ReadOp) → Result o → Value
  initial_valid : ∀ i : Init, Valid (initial i)
  replace_valid : ∀ w s, Valid s → Valid (replace w s).1
  encodeRead_injective : ∀ o (x y : Result o),
    encodeRead o x = encodeRead o y → x = y
  observe_detached : ∀ (ℓ : Loc) o s,
    Valid s → NoRef ℓ (encodeRead o (observe o s))
-- the library's class has all these fields, at these types
example [i : LawfulStateVar σ I R W] : Shown σ I R W := { i with }
```

## The lawful state variable
- The obligations are ==fields of the class==: an instance that cannot prove them does not exist.
- Valid initial states; validity kept by every write.
- Reads encode injectively — a constant encoding cannot hide a reference.
- Every read of a valid state is detached: `NoRef ℓ` for every location.
```the class
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar

variable {σ I R W : Type} [inst : LawfulStateVar σ I R W]

example (w : W) (s : σ) (h : inst.Valid s) :
    inst.Valid (inst.replace w s).1 :=
  inst.replace_valid w s h

example (ℓ : Loc) (o : R) (s : σ) (h : inst.Valid s) :
    NoRef ℓ (inst.encodeRead o (inst.observe o s)) :=
  inst.observe_detached ℓ o s h
```

## The structured theorems, for every lawful type
- Share conservation, exclusion, join, replay and schedule independence are restated over any instance.
- A single-root heap: reads leave it unchanged, writes change only their own cell, ==snapshots persist==.
- The array is an instance, and bridge theorems prove Model 2 computes exactly what Model 1's executor does.
```generic snapshot
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar

variable {σ I R W : Type} [inst : LawfulStateVar σ I R W]

-- read, write, read: each value bound to its own heap
example {ℓ : Loc} {o : R} {w : W} {h h' : Heap σ} {b : Bool}
    {v v' : inst.Result o}
    (hr : ReadAt inst ℓ o h h v) (hw : WriteAt inst ℓ w h h' b)
    (hr' : ReadAt inst ℓ o h' h' v') :
    ∃ s, At ℓ s h ∧ v = inst.observe o s ∧
      v' = inst.observe o (inst.replace w s).1 :=
  snapshot_after_write hr hw hr'
```

## The laws are not vacuous
- A read that returns `.loc s`, a write that leaves the valid states, an encoding that forgets the result: each is ==proved== to violate its obligation.
- And a read result is only conditionally safe: `pure (.loc ℓ)` is a client value no law can forbid.
- `safe_result`: if each continuation keeps a predicate, so does the result — stated, not assumed.

```countermodels
import ScidoniaTest.StateVar
open Scidonia.FracPerm.StateVar

-- A read returning a reference fails the detachment law.
example : ¬ (∀ (ℓ s : Nat), NoRef ℓ (Value.loc s)) :=
  ScidoniaTest.StateVar.bad_read_rejected
```

