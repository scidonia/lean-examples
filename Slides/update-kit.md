# Writing through a path

## A compiler optimisation that looks like a side effect
- Lean has no mutable state. `a.set! i v` is a function: it denotes a ==new== array, and no term in the language can change a value that already exists.
- Yet the compiled code mutates. When the array has one reference, `Array.set!` compiles to a store into the array's buffer and a pointer to that same buffer comes back.
- Both statements are true because the mutation is ==unobservable==: if the old value has exactly one reference, nothing in the program can distinguish "the same object with one slot changed" from "a new object, copied".

```the meaning is pure
import Scidonia.FracPerm

-- What the source means: a new array, of the same size, with one slot changed.
#guard ((#[1, 2, 3] : Array UInt64).set! 0 7)[0]? == some 7
#guard ((#[1, 2, 3] : Array UInt64).set! 0 7).size == 3
-- and the value it was applied to still holds what it held
#guard (#[1, 2, 3] : Array UInt64)[0]? == some 1
```

## When mutating is legal
- The compiler asks one question at every mutation site: ==is this object's reference count exactly 1 here?==
  - count 1 → the old value is dead, so mutating it cannot be observed: store into it.
  - count 2 or more → something may still read the old value: allocate a copy.
  - count 0 → a compile-time constant, which can never be unique: always copy.
- The count comes from ==use counts in the code==, not from what the program means. A value used twice in one expression, an alias kept alive, or a projection held across the call is enough to force the copy.

## So: how do we make the mutation unobservable?
- "Unobservable" is not a property of our intent. It is exactly: ==no other reference to the object exists at that moment==.
- And we cannot make the compiler mutate — we can only make its legality condition true where we want the mutation. The same definition mutates through one caller and copies through another; only the ownership differs.
- Since the compiler reads ownership off the code, this is a *coding discipline*: and a discipline can be built into an interface, so that the shapes that lose the mutation cannot be written.

## What this tutorial does
- The first half builds the kit of a write, piece by piece, from the definitions: an address, the focus type, a context to rebuild, the new value, and the pair of traversals that decide whether the address is real and perform the update.
- The kit is arranged for exactly the three things unobservability needs:
  - the state is unreachable except through the interface, so no client can hold an alias to it;
  - a read returns an ==observation== — a value built from atoms — so nothing sharing the state's memory can escape and stay live;
  - the write takes the focused node out, checks it is exclusively owned, updates it and puts it back, returning the state alone: one owner, one candidate cell.
- The second half shows how it behaves: what the compiler emitted, which shapes stay in place, which copy, and what the harness asserts.

## What a write needs
- An **address**: a path into the state, typed by the layout it walks.
- The **focus type**: what sits at the end of the path.
- A **context**: everything else, in a form that can be rebuilt.
- The **new value**: and here is the first design decision — a write installs an *observation*, never a state.
- Plus a predicate saying whether the path addresses anything, since an array index can be out of bounds.

Each of the next slides is one of those pieces, quoted from `Scidonia/FracPerm/StateVar/Layout5.lean` so that the deck cannot drift from the library.

## The new value: an observation
- `ObsDesc` is the code for what a write may install and a read may return.
- Four atoms and three ways to combine them — ==no array, no struct of the state, no reference==.
- This is what makes a client alias impossible: there is no way to write a piece of state into the state.

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

## An observation's meaning
- `ObsEl` gives each code its type, by recursion on the code.

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

## The state: a layout
- `Layout` is the code for what the state *is*: a stored observation, a binary struct, or an array of a layout.

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

## The state type: State
- `State` interprets a layout as the Lean type the program holds — pairs, and arrays. These are the types Lean updates in place when they are uniquely owned; see the second half of this tutorial.

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- The state type a layout denotes: an element of the observation universe, a
pair of states, or an array of states. -/
abbrev State : Layout → Type
  | .leaf o => ObsEl o
  | .struct a b => State a × State b
  | .arr a => Array (State a)
```

## The address: a typed path
- `Path d` is an address inside layout `d`. The struct steps exist only under a `struct`; an array step carries an index, which is the one step whose validity depends on a particular state.
- `At` is the layout at the end of the path — the focus type. A write must supply a value of exactly that type, which is what makes the recursion well typed.

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

## An address a write may use
- `ObsPath d` is a path *together with a proof* that it ends at an observation leaf.
- That proof field is the whole reason a write can only install an observation: a path to an array or a struct has no such proof, so such a write cannot be written down.
- It is also why a whole-array read is a type error.

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

## What to rebuild: the one-hole context
- A write does not "find the root and change a field": it takes the state apart along the path, keeps everything else, and puts it back.
- `Context d p` is exactly "everything except the focus" — the *derivative* of the layout: at a struct one component holds the hole and the other is kept whole; at an array the array the take-out left is kept, together with the index that puts the focus back.
- It is private: it is the write's *specification*, not part of a client's surface.

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

## Putting the focus back: plug
- `plug` fills the hole: the recursion on the context rebuilds the state with the new focus in place of the old one.
- `plug` is total; the array case uses the index bound the context carries.

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

## Taking an element out: the owned exchange
- The array case cannot simply read slot `i` and write it back: the array would still hold the element, so a write inside it would copy.
- `takeOut` is an owned `Array.swapAt`: the array keeps its size and every other slot, and the element comes back as the sole owner.
- Note the comment: the *array's* exclusivity is not the *element's* — another slot may alias it — so the caller checks the extracted element before writing inside it. That check is in the update (next slides).

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- Take the element at `i` out of an array, leaving `d` in its place: the array
keeps its size and every other slot. When the array is exclusively owned the
exchange is an update in place and hands the element back; the array's
exclusivity is not the element's, though — the take-out replaces one slot, and
another slot may still point at the same object — so the caller checks the
extracted element before writing inside it. Without the array's exclusivity the
exchange copies the array, and the array the caller kept still holds the
element. -/
private def takeOut (s : Array α) (i : Nat) (h : i < s.size) (d : α) : Array α × α :=
  let r := s.swapAt i d h
  (r.2, r.1)
```

## Does the path address anything?
- An array index may be out of bounds. `inBounds` decides that first, as a pure traversal: it reads the elements along the path and never copies an array.
- Deciding first is what lets the update itself be total, and what lets a failed write return the original state unchanged.

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- Whether every index along a path is in bounds. A pure traversal: it reads
an array's element and never copies the array. -/
private def inBounds : {d : Layout} → (p : Path d) → State d → Bool
  | _, .here, _ => true
  | _, .left q, s => inBounds q s.1
  | _, .right q, s => inBounds q s.2
  | _, .index i q, s => if h : i < s.size then inBounds q s[i] else false
```

## The update itself: a recursion over the path
- One clause per path constructor. `here` replaces the focus. `left` and `right` destructure the struct cell and rebuild it from the updated component — returning the *state alone*, which is what lets the compiler reuse the cell. `index` takes the element out, ==checks the extracted focus==, recurses, and puts it back.
- The new focus is threaded through as a *value*, not as a function of the old state, so the write path allocates no closure.

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- The fused update: recurse along the path, rebuilding each struct cell from
its updated component, and take the selected element out of an array, check the
extracted focus, update it and put it back. The new focus is threaded through
the recursion as the focus of the path rather than as a function of the old one,
so the write path allocates no closure. The result is the state alone, so a
struct cell can be reused for the struct the recursion rebuilds — which a
`State d × Bool` result would prevent, because the pair the compiler then reuses
is the transient one. -/
private def setAt : {d : Layout} → (p : Path d) → State (At p) → State d → State d
  | _, .here, y, _ => y
  | _, .left q, y, (u, v) => (setAt q y u, v)
  | _, .right q, y, (u, v) => (u, setAt q y v)
  | _, .index i q, y, s =>
      if h : i < s.size then
        match takeOutAt (assertExclusiveArray openSite s) i h (stateDefault _) with
        | ⟨(sib, focus), hbound⟩ =>
          plugAt sib i hbound (setAt q y (assertExclusive structSite focus))
      else s
```

## The public write
- `setLeaf` gates on `inBounds`, then runs the update, casting the observation to the focus type exactly once; a failed write returns the state it was given.
- The client never sees `Context`, `plug`, `takeOut`, `takeOutAt`, `plugAt`, `inBounds` or `setAt`: the private pieces are the specification and the machinery, and this is the whole of the write's public face.

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
def setLeaf {d : Layout} (p : ObsPath d) (x : ObsEl p.obs) (s : State d) :
    State d × Bool :=
  if inBounds p.path s then
    (setAt p.path (cast (congrArg State p.leaf.symm) x) s, true)
  else (s, false)
```

## The update meets the specification
- The point of the zipper is that it is the *specification*; the point of `setAt` is that it runs. This theorem is the bridge: on a state the private `open` takes apart, `setAt` is `open`'s context plugged with `open`'s focus.
- Everything else follows from it — reading back what was written, a failed write leaving the state alone, and a write leaving disjoint paths' reads unchanged.

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- The fused update agrees with the zipper specification: on a state the
private `open` takes apart, `setAt` is the context `open` reported plugged with
the focus it reported. -/
private theorem setAt_spec : ∀ {d : Layout} (p : Path d) (s : State d) (c : Context d p)
    (f : State (At p)) (y : State (At p)),
    «open» p s = .ok (c, f) → setAt p y s = plug c y := by
  intro d p
  induction p with
  | here =>
    intro s c f y hopen
```

## Reading it back
- A read follows the same paths and returns the library's encoding of the leaf, or `none` when the path addresses nothing.
- The theorems a client gets about writes: `setLeaf_failed` (a failed write leaves the state alone), `snapshot_after_setLeaf` (the old value is bound to the old state, the new read to the write's operand), and `read_frame` (a write at a disjoint path changes no other read).

```@../lean/Scidonia/FracPerm/StateVar/Layout5.lean
/-- Read a leaf path: the library's encoding of the observation at the path's
end, or `none` when the path does not address anything. The result is an
immutable `Value`; there is no route from here to the state or a subtree. -/
def read? {d : Layout} (p : ObsPath d) (s : State d) : Option Value :=
  (leafAt? p.path p.obs p.leaf s).map (encodeObs p.obs)
```
