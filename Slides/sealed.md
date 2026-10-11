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

## The kit
- To make the library own reads, the description must be data the library can compute with: a *code* for each type, and a function interpreting the code. This is the levitation pattern.
- The kit has two universes, one for what the state is and one for what a read may return. Typed paths connect them, with a predicate saying when a path ends at an observation.
- Then a canonical encoding, the predicates the laws are stated in, and a derivative for writes.
- Each of the next slides gives one piece, checked against the library.

```the kit's signatures
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar Layout5

example : ObsDesc → Type := ObsEl          -- observation codes
example : Layout → Type := State           -- layout codes
example : Layout → Type := Path            -- addresses
example {d : Layout} : Path d → Layout := At
example : (o : ObsDesc) → ObsEl o → Value := encodeObs
example : Loc → Value → Prop := NoRef
example {d : Layout} : Path d → Path d → Prop := Disjoint
```

## Kit 1 — the observation universe
- `ObsDesc` is the code for what a read may return: atoms (unit, naturals, words, booleans), closed under sum, option and pair.
- `ObsEl` interprets a code as a Lean type, one clause per constructor.
- No code denotes an array, a struct of the state, or a location. That is the whole point: ==a type outside this universe cannot be a read result==.
- The panel's `code` function matches every constructor, so it compiles only if the library has exactly these.

```ObsDesc and ObsEl
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar.Layout5

def code : ObsDesc → String
  | .unit => "unit" | .nat => "nat" | .uint => "word" | .bool => "bool"
  | .sum _ _ => "sum" | .option _ => "option" | .pair _ _ => "pair"

example : ObsEl .uint = UInt64 := rfl
example : ObsEl .bool = Bool := rfl
example (a b : ObsDesc) : ObsEl (.sum a b) = (ObsEl a ⊕ ObsEl b) := rfl
example (a : ObsDesc) : ObsEl (.option a) = Option (ObsEl a) := rfl
example (a b : ObsDesc) : ObsEl (.pair a b) = (ObsEl a × ObsEl b) := rfl
```

## Kit 2 — the layout universe
- `Layout` is the code for what the state *is*: a stored observation (`leaf`), a binary `struct`, or an `arr` of a layout. Nesting gives arrays of structs, arrays of arrays, and so on.
- `State` interprets a layout as the Lean type the program actually holds: pairs and `Array`s, which Lean updates in place when they are uniquely owned.
- Layouts may contain arrays; observations may not. The asymmetry between the two universes is what makes reads safe.

```Layout and State
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar.Layout5

def shape : Layout → String
  | .leaf _ => "leaf" | .struct _ _ => "struct" | .arr _ => "array"

example (o : ObsDesc) : State (.leaf o) = ObsEl o := rfl
example (a b : Layout) : State (.struct a b) = (State a × State b) := rfl
example (a : Layout) : State (.arr a) = Array (State a) := rfl

example : State (.arr (.struct (.leaf .uint) (.leaf .uint)))
    = Array (UInt64 × UInt64) := rfl
```

## Kit 3 — typed paths
- `Path d` is an address inside layout `d`, a datatype indexed by the code it walks. `left` and `right` only exist under a `struct`, and `index i` only under an `arr`.
- `At p` computes the layout at the end of the path.
- The struct steps are checked statically by the index. Only an array index can fail, at run time, when it is out of bounds.

```Path and At
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar.Layout5

def step : {d : Layout} → Path d → String
  | _, .here => "here" | _, .left _ => "left"
  | _, .right _ => "right" | _, .index _ _ => "index"

example {a b : Layout} (p : Path a) : Path (.struct a b) := .left p
example {a : Layout} (i : Nat) (p : Path a) : Path (.arr a) := .index i p

example (d : Layout) : At (Path.here : Path d) = d := rfl
example {a b : Layout} (p : Path a) :
    At (Path.left (b := b) p) = At p := rfl
example {a : Layout} (i : Nat) (p : Path a) :
    At (Path.index i p) = At p := rfl
```

## Kit 4 — observable paths and the canonical encoding
- `ObsPath d` is a path *together with a proof* that it ends at an observation leaf: `At path = .leaf obs`. A path to an array or a struct has no such proof.
- `encodeObs` is the library's one encoding from observations to `Value`. It has a clause per code and none produces `.loc`.
- An instance author supplies neither the predicate nor the encoding.

```ObsPath and encodeObs
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar Layout5

structure Shown (d : Layout) where
  path : Path d
  obs : ObsDesc
  leaf : At path = .leaf obs
example (p : ObsPath d) : Shown d := { p with }

example (n : UInt64) : encodeObs .uint n = .uint n := rfl
example (a b : ObsDesc) (x : ObsEl a) :
    encodeObs (.sum a b) (.inl x) = .inl (encodeObs a x) := rfl
example (a b : ObsDesc) (x : ObsEl a) (y : ObsEl b) :
    encodeObs (.pair a b) (x, y) = .pair (encodeObs a x) (encodeObs b y) := rfl
```

## Kit 5 — the predicates
- `NoRef ℓ v`: `v` contains no `.loc ℓ`, however deeply nested. This is the detachment the laws demand.
- `Disjoint p q`: neither path extends the other, so the paths are not equal, not ancestor and descendant, and not through the same index. This is what frames are stated over.
- From the clauses alone, every encoded observation is detached, for every code. That is proved once, by induction on `ObsDesc`.

```NoRef and Disjoint
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar Layout5

example (ℓ k : Loc) : NoRef ℓ (.loc k) = (k ≠ ℓ) := rfl
example (ℓ : Loc) (x y : Value) :
    NoRef ℓ (.pair x y) = (NoRef ℓ x ∧ NoRef ℓ y) := rfl

example {d : Layout} (p q : Path d) :
    Disjoint p q = ((∀ r : Path (At p), q ≠ p.append r) ∧
                    (∀ r : Path (At q), p ≠ q.append r)) := rfl

example (ℓ : Loc) (o : ObsDesc) (x : ObsEl o) : NoRef ℓ (encodeObs o x) :=
  encodeObs_noRef ℓ o x
```

## Kit 6 — the derivative, and the operations
- A write needs a one-hole context: the state with the addressed part removed. It is the derivative of the layout:
  - at a leaf, the hole is the whole value;
  - `∂(struct a b) = ∂a × State b + State a × ∂b`, so one side keeps a hole and the other is kept whole;
  - `∂(arr a) = index × siblings × ∂a`, the element taken out and the array kept with a placeholder.
- `open` splits a state into a context and its focus, and `plug` fills the hole. Both are private: they are the specification, and the executed `setLeaf` is proved equal to them.
- Clients get two operations, and theorems about them.

```operations
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar Layout5

example {d : Layout} (p : ObsPath d) : State d → Option Value := read? p
example {d : Layout} (p : ObsPath d) (x : ObsEl p.obs) :
    State d → State d × Bool := setLeaf p x

-- a write leaves every disjoint path's read unchanged
example {d : Layout} (p q : ObsPath d) (s s' : State d) (new : ObsEl p.obs)
    (hd : Disjoint p.path q.path) (hw : setLeaf p new s = (s', true)) :
    read? q s' = read? q s :=
  read_frame p q s s' new hd hw
```

## Using the kit
- A concrete layout, an observable path, and a read.
- At an array root there is no observable path, so a whole-array read is a ==type error==.

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
