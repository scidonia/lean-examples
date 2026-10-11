# Model 5: paths and sealed state variables

## A lawful instance can still leak
- `LawfulStateVar` lets the author choose `observe` *and* `encodeRead`.
- Encode an array as nested pairs of words: injective, and no `.loc` anywhere — all four laws hold.
- Yet `observe () s := s` hands back ==the protected array itself==. Lean's logic sees values, not identities: an alias and a copy are equal.

```the countermodel
import ScidoniaTest.Model5
open Scidonia.FracPerm.StateVar

-- lawful, and its read is the state
example (a : Array UInt64) :
    LawfulStateVar.observe
      (self := ScidoniaTest.Model5.leakyArrayStateVar) () a = a :=
  ScidoniaTest.Model5.leakyArray_read_returns_state a
```

## Reads are addresses, writes are zippers
- A read follows a typed path — field, index, field — to a leaf, and returns a *detached* value there.
- A write opens a zipper at the path: take the element out, update it while it is the only reference, put it back.
- McBride: the one-hole contexts of a datatype are its ==derivative==, computed from the description.
- The fix for the leak: the *library* owns reading, writing and encoding; authors only describe.

## Layouts and observations
- A **layout** is the state's shape: a leaf, a binary struct, or an array.
- An **observation** is what a read may return: unit, nat, words, booleans, and sums, options and pairs of them.
- Observations contain ==no array, no struct of the state, no reference== — by construction of the type.

```two universes
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar.Layout5

-- an array of structs of two words
example : State (.arr (.struct (.leaf .uint) (.leaf .uint)))
    = Array (UInt64 × UInt64) := rfl

-- what a read may return
example : ObsEl (.option (.pair .uint .bool))
    = Option (UInt64 × Bool) := rfl
```

## Paths, and the read that cannot be written
- `ObsPath d`: a path whose end is *proved* to be an observation leaf.
- At an array root there is no such proof — a whole-array read is a ==type error==.
- Every read result is detached: `encodeObs` has no `.loc` case, for every observation.

```reads
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar Layout5

abbrev Pairs : Layout := .arr (.struct (.leaf .uint) (.leaf .uint))

-- the first field of the struct at index 3
def p₃ : ObsPath Pairs := ⟨.index 3 (.left .here), .uint, rfl⟩

#guard decide (read? p₃ (#[(0, 0), (1, 1), (2, 2), (7, 9)] : State Pairs)
  = some (.uint 7))

example (o : ObsDesc) :
    At (Path.here : Path (.arr (.leaf .uint))) ≠ .leaf o :=
  array_root_not_observable o
```

## Writes: take out, update, put back
- The element is exchanged out of its array with `swapAt`, leaving a placeholder.
- It is checked to be exclusively owned, updated, and put back.
- The executed update is one fused recursion, ==proved equal== to the zipper specification; the zipper itself is private.
- Snapshots persist, and a write leaves disjoint paths' reads unchanged.

```the snapshot
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar Layout5

example {d : Layout} (p : ObsPath d) (s s' : State d)
    (old : Value) (new : ObsEl p.obs)
    (hread : read? p s = some old)
    (hwrite : setLeaf p new s = (s', true)) :
    read? p s = some old ∧
      read? p s' = some (encodeObs p.obs new) :=
  snapshot_after_setLeaf p s s' old new hread hwrite
```

## The sealed class
- An instance gives only a layout and a proof that its type ==is== that layout's state type.
- Reads, writes and the encoding are the library's; the state-variable laws are derived, not proved per instance.
- The equality is a proof, so its casts erase: no conversion, no copy at run time.

```class SealedStateVar
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar Layout5

class Shown (σ : Type) where
  layout : Layout
  rep : σ = State layout

-- the library's class has all these fields, at these types
example [i : SealedStateVar σ] : Shown σ := { i with }

-- an array of structs is sealed in one line
example : SealedStateVar (Array (UInt64 × UInt64)) :=
  ⟨.arr (.struct (.leaf .uint) (.leaf .uint)), rfl⟩
```

## No field to leak through
- The leaky read cannot be written: the class has no `observe` to put it in.
- Nor can a type claim a layout it is not: `rep` must be an equality the elaborator accepts.

```rejected
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar

/--
error: `observe` is not a field of structure `SealedStateVar`
-/
#guard_msgs in
instance : SealedStateVar (Array UInt64) where
  layout := .arr (.leaf .uint)
  rep := rfl
  observe := fun _ s => s
```

## In place, measured
- Path writes on a fresh `Array (UInt64 × UInt64)`: the array and the written struct ==keep their addresses== — asserted.
- With a live alias, the struct is copied and the alias keeps its values; with checking on, an aliased element aborts at the focus.
- Two compiler surprises, each caught by the harness: a take-out pair still alive at the check, and struct reuse landing on a temporary `(state, Bool)` pair instead of the stored cell.
- Proved: detachment, snapshots, frames, derived laws. Checked at run time: in-place identity of the library's own primitives. Trusted: the compiler.
