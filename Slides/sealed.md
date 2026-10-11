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
- Each of the next slides gives one piece. The definitions are quoted ==verbatim from this repository's source==, so the deck build fails if the library changes.

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

## Kit 1 — the observation codes
- `ObsDesc` is the code for what a read may return: four atoms, and three ways to combine them.
- Quoted from `Scidonia/FracPerm/StateVar/Layout5.lean`. A quotation must be verbatim, so the deck build ==fails== if the library's definition changes.
- No code is an array, a struct of the state, or a reference, so a type outside this universe cannot be a read result.

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
inductive ObsDesc where
  /-- The unit type. -/
  | unit
  /-- The type of naturals. -/
  | nat
  /-- The type of unsigned machine words. -/
  | uint
  /-- The type of booleans. -/
  | bool
  /-- A sum of two described types. -/
  | sum (left right : ObsDesc)
  /-- An optional described type. -/
  | option (elem : ObsDesc)
  /-- A pair of two described types. -/
  | pair (left right : ObsDesc)
deriving DecidableEq, Repr
```

## Kit 2 — the observation interpretation
- `ObsEl` gives each code its meaning, by recursion on the code: one clause per constructor.
- The atoms are immutable data, and sum, option and pair are built from them. ==No clause denotes an array or a struct of the state==, which is what makes every `ObsEl o` a type of values.
- A read returns an element of one of these types and nothing else.

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- The type a leaf description denotes. Units, naturals, words and booleans
are immutable data; a sum, option or pair is built from them. No case is an
array, a struct or a reference. -/
abbrev ObsEl : ObsDesc → Type
  | .unit => Unit
  | .nat => Nat
  | .uint => UInt64
  | .bool => Bool
  | .sum a b => Sum (ObsEl a) (ObsEl b)
  | .option a => Option (ObsEl a)
  | .pair a b => ObsEl a × ObsEl b
```

## Kit 3 — the layout codes
- `Layout` is the code for what the state *is*: a stored observation (`leaf`), a binary `struct` — so arbitrarily many fields by nesting — or an `arr` of a layout.
- Codes may contain arrays; observations may not. That asymmetry is what makes reads safe.

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
inductive Layout where
  /-- A leaf of the observation universe. -/
  | leaf (o : ObsDesc)
  /-- A binary product of two layouts. -/
  | struct (left right : Layout)
  /-- An array of a layout. -/
  | arr (elem : Layout)
deriving DecidableEq, Repr
```

## Kit 4 — the state type
- `State` is the ==definition of the state type==: it interprets a layout as the Lean type the program holds — pairs, and `Array`s.
- This is the `State layout` the sealed class asks a type to *be*, in `rep : σ = State layout`.
- These are the types Lean updates in place when they are uniquely owned, which is what the `inplace` harness measures.
- Nesting is unbounded, so an array of structs of two words denotes `Array (UInt64 × UInt64)`.

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- The state type a layout denotes: an element of the observation universe, a
pair of states, or an array of states. -/
abbrev State : Layout → Type
  | .leaf o => ObsEl o
  | .struct a b => State a × State b
  | .arr a => Array (State a)
```

## Kit 5 — typed paths
- `Path d` is an address inside layout `d`, indexed by the code it walks: `left` and `right` only exist under a `struct`, and `index i` only under an `arr`.
- `At` computes the layout at the end of a path.
- The struct steps are checked statically by the index. Only an array index can fail, at run time, when it is out of bounds.

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
inductive Path : Layout → Type where
  /-- The path to the whole layout. -/
  | here {d : Layout} : Path d
  /-- Descend into the left component of a struct. -/
  | left {a b : Layout} (p : Path a) : Path (.struct a b)
  /-- Descend into the right component of a struct. -/
  | right {a b : Layout} (p : Path b) : Path (.struct a b)
  /-- Descend into element `i` of an array. -/
  | index {a : Layout} (i : Nat) (p : Path a) : Path (.arr a)
deriving DecidableEq

/-- The layout at the end of a path. -/
abbrev At {d : Layout} : Path d → Layout
  | .here => d
  | .left p => At p
  | .right p => At p
  | .index _ p => At p
```

## Kit 6 — observable paths and the canonical encoding
- `ObsPath d` is a path *together with a proof* that it ends at an observation leaf: `At path = .leaf obs`. A path to an array or a struct has no such proof, so a whole-array read cannot even be written down.
- `encodeObs` is the library's one encoding from observations to `Value`. It has a clause per code ==and none produces `.loc`==.
- An instance author supplies neither the predicate nor the encoding.

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- A read path: a path together with the leaf description its end must have.
The proof field is why no `ObsPath` exists for a `.struct` or `.arr` root —
`At p = .leaf o` has no solution there — so a whole-array read cannot be
written down, let alone performed. -/
structure ObsPath (d : Layout) where
  /-- The path. -/
  path : Path d
  /-- The leaf description at the path's end. -/
  obs : ObsDesc
  /-- The end of the path is that leaf. -/
  leaf : At path = .leaf obs
```

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
def encodeObs : (o : ObsDesc) → ObsEl o → Value
  | .unit, _ => .unit
  | .nat, n => .nat n
  | .uint, n => .uint n
  | .bool, b => .bool b
  | .sum a _, Sum.inl x => .inl (encodeObs a x)
  | .sum _ b, Sum.inr y => .inr (encodeObs b y)
  | .option _, none => .none
  | .option a, some x => .some (encodeObs a x)
  | .pair a b, (x, y) => .pair (encodeObs a x) (encodeObs b y)
```

## Kit 7 — the predicates
- `NoRef ℓ v`: `v` contains no `.loc ℓ`, however deeply nested. This is the detachment the laws demand.
- `Disjoint p q`: neither path extends the other, so the paths are not equal, not ancestor and descendant, and not through the same index. This is what frames are stated over.
- From the clauses alone, every encoded observation is detached, for every code: `encodeObs_noRef`, proved once by induction on `ObsDesc`.

```@../lean/Scidonia/FracPerm/StateVar/Value.lean
def NoRef (ℓ : Loc) : Value → Prop
  | .loc k    => k ≠ ℓ
  | .some v   => NoRef ℓ v
  | .inl v    => NoRef ℓ v
  | .inr v    => NoRef ℓ v
  | .pair x y => NoRef ℓ x ∧ NoRef ℓ y
  | _         => True
```

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- Two paths into the same layout are disjoint when neither goes through the
other: `q` is not `p` extended by anything, and `p` is not `q` extended by
anything. This excludes the equal paths and every ancestor/descendant pair,
including two paths through the same array index. -/
def Disjoint {d : Layout} (p q : Path d) : Prop :=
  (∀ r : Path (At p), q ≠ Path.append p r) ∧ (∀ r : Path (At q), p ≠ Path.append q r)
```

## Kit 8 — the one-hole context
- A write needs the state with the addressed part removed: the *one-hole context*, which is the ==derivative== of the layout.
- At a leaf the hole is the whole value; at a struct one component keeps the hole and the other is held whole, `∂(struct a b) = ∂a × State b + State a × ∂b`; at an array the element is taken out and the array is held with a placeholder, together with the index that puts it back, `∂(arr a) = index × siblings × ∂a`.
- It is private: it is the *specification* of a write, not part of a client's surface.

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- The one-hole context of a path: the parts of a state other than the focus.
The array case keeps the array the take-out left and the focus's index. -/
private inductive Context : (d : Layout) → Path d → Type where
  /-- The whole state is the focus. -/
  | here (d : Layout) : Context d .here
  /-- The left component is inside; the right is held. -/
  | left {a b : Layout} {p : Path a} (inner : Context a p) (right : State b) :
      Context (.struct a b) (.left p)
  /-- The right component is inside; the left is held. -/
  | right {a b : Layout} {p : Path b} (left : State a) (inner : Context b p) :
      Context (.struct a b) (.right p)
  /-- Element `i` is inside; the array the take-out left is held, and
  `i < siblings.size` is what lets `plug` land the focus back at the index. -/
  | index {a : Layout} {p : Path a} (i : Nat) (siblings : Array (State a))
      (bound : i < siblings.size) (inner : Context a p) : Context (.arr a) (.index i p)
```

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- Fill a one-hole context with a focus: the state the context describes, with
the focus in its place. -/
private def plug : {d : Layout} → {p : Path d} → Context d p → State (At p) → State d
  | _, _, .here _, x => x
  | _, _, .left inner right, x => (plug inner x, right)
  | _, _, .right left inner, x => (left, plug inner x)
  | _, _, .index i siblings bound inner, x =>
      plugAt siblings i bound (plug inner x)
```

## Kit 9 — the operations
- `read?` returns the library's encoding of the observation at the path, or `none` when the path addresses nothing.
- `setLeaf` returns the new state and whether the write took effect. It asks `inBounds` first, then runs the fused update, and casts the observation to the focus type exactly once.
- The theorems about them: `read_detached`, `snapshot_after_setLeaf` (the old value is bound to the old state), `read_frame` (disjoint paths), `setLeaf_failed` (a failed write leaves the state alone).

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- Read a leaf path: the library's encoding of the observation at the path's
end, or `none` when the path does not address anything. The result is an
immutable `Value`; there is no route from here to the state or a subtree. -/
def read? {d : Layout} (p : ObsPath d) (s : State d) : Option Value :=
  (leafAt? p.path p.obs p.leaf s).map (encodeObs p.obs)
```

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
def setLeaf {d : Layout} (p : ObsPath d) (x : ObsEl p.obs) (s : State d) :
    State d × Bool :=
  if inBounds p.path s then
    (setAt p.path (cast (congrArg State p.leaf.symm) x) s, true)
  else (s, false)
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
