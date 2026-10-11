/-
Model 5: paths, detached observations, and take-out writes.

The state variable of `Scidonia.FracPerm.StateVar.Class` is a single root cell
whose value is an element of one description. This module adds a *layout*: a
type with structure whose state is a binary product or an array, and a *path*
into it. The design has four parts:

* `Layout` and `State` describe a state's shape: a leaf of the observation
  universe `ObsDesc`, a binary `struct`, or an `arr` of a layout. A read path
  ends only at a leaf of `ObsDesc`, so a read result is a value of the separate
  observation universe `ObsEl o`, which contains no array, struct or reference.

* `Path`, `At`, `ObsPath` and the zipper (`Context`, `open`, `plug`) are the
  mathematical vocabulary: a path is an address, `open` takes a state apart at a
  path, and `plug` puts a focus back. They are private and are the write's
  *specification*: `open` returns the raw focus at a path's end, so exporting
  them would let a client keep a mutable node (an inner array) and read past a
  leaf. The public surface is `read?`, which returns `Option Value` and never a
  state or a subtree, and `setLeaf`, proved equal to the zipper's path
  replacement.

* `encodeObs` is the library's one encoding of a leaf observation as a `Value`,
  and `read?` is the only route from a state to a `Value`: its traversal
  (`leafAt?`, private) obtains the raw focus and immediately encodes the
  immutable leaf. An `ObsPath` cannot even be built for a mutable node, since
  `At p = .leaf o` has no solution for an `.arr` or `.struct` end.

* `setLeaf` is the write. It first asks `inBounds` whether the path addresses
  anything — a pure traversal that reads arrays and never copies one — and then
  runs `setAt`, a structurally recursive update that returns the state alone and
  threads the new focus through the recursion as a value rather than as a
  function of the old one, so the write path allocates no closure: at a struct
  it destructures the pair and rebuilds it from the updated component
  (`let (a, b) := s; (go a, b)`), and at an array it is the take-out, the focus
  check, the recursion on the extracted element and the put-back. Keeping the
  pair out of the recursion is what lets Lean's reset/reuse pass rewrite the
  struct cell in place instead of allocating a new one. `setLeaf` is proved
  equal to the zipper's path replacement, so every theorem stated about it
  holds of the specification.

The array case is a *take-out* update. `takeOut` is an owned `Array.swapAt`
exchange that leaves the layout's placeholder in the selected slot and hands the
element back, so the array keeps its size and every other slot; `plugAt` is the
inverse exchange, and it puts a focus back into that slot. The pair `takeOut`
returns is destructured before anything is checked or recursed into, and the
path below it is taken apart on the extracted element itself. The array's
exclusivity is not the element's: the take-out replaces one slot, and a caller
that built an aliased array can leave another slot pointing at the same object.
If the path below cannot be opened, the state `open` reported is put straight
back, so the failure reports the original array.

Two checks guard the mutation, and both are the library's `assertExclusive`: the
*array*, before the take-out, because a shared array is what a write would copy
whole; and the *extracted focus*, before the update below it runs, because a
shared element — a spare slot, or an alias a caller kept — is what a write inside
it would copy. Both checks are the identity in the logic, so no theorem mentions
them; compiled, they turn a write that would copy into a terminated process.
Whether a write updates in place is run-time evidence from `ScidoniaInPlace`,
not a theorem. Two instruments report it, and they answer different questions:
the generated C of `setAt`'s array case — the recursion `setLeaf` executes —
shows the ownership and the order — the pair the take-out returned converted to
its two locals and released, the focus check after it, the recursion on the
check's result, and the put-back — while the harness's `addressIO` observations,
with the assertions it puts on them, are what establishes that an address is
unchanged or changed. `open`'s index case writes the same sequence down as the
zipper specification `setLeaf` is proved equal to; it is not the code the write
runs.

Nothing here modifies `Desc`, `El`, `Described`, `LawfulStateVar` or the
Models 1–4 modules: the adapter `describedLayoutStateVar` is a value of the
existing class built from library definitions, not a new instance for a
user-supplied encoder.
-/
import Scidonia.FracPerm.StateVar.Heap
import Scidonia.FracPerm.InPlace

namespace Scidonia.FracPerm.StateVar

namespace Layout5

/-! ## The observation universe and layouts

`ObsDesc` is deliberately closed: unit, natural, machine word, boolean, sum,
option and pair. It has no constructor for an array, a struct or a reference, so
an element of `ObsEl o` is immutable data and a read that returns one cannot
hand back a mutable part of the state. `Layout` is the state's shape; a read
path ends at a `.leaf`, and `State (.leaf o)` is `ObsEl o` by definition. -/

/-- A description of a read leaf: the closed observation universe. -/
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

/-- The shape of a state: a leaf of the observation universe, a binary struct
(so arbitrarily many fields by nesting), or an array of a layout. -/
inductive Layout where
  /-- A leaf of the observation universe. -/
  | leaf (o : ObsDesc)
  /-- A binary product of two layouts. -/
  | struct (left right : Layout)
  /-- An array of a layout. -/
  | arr (elem : Layout)
deriving DecidableEq, Repr

/-- The state type a layout denotes: an element of the observation universe, a
pair of states, or an array of states. -/
abbrev State : Layout → Type
  | .leaf o => ObsEl o
  | .struct a b => State a × State b
  | .arr a => Array (State a)

/-! ## Paths

A path is an address in a layout. `Path.index` is dynamic: its index is a
number, and whether it addresses anything is a property of a particular state,
checked when the path is opened. Every other step is statically checked by the
layout indices. `At p` is the layout at the end of `p`. -/

/-- A path into a layout. `index i p` descends into the array's element `i`,
which may be out of bounds for a particular state; the other steps are total. -/
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

/-- Concatenate two paths: the steps of the first, then the steps of the second
from the layout the first ends at. -/
def Path.append : {d : Layout} → (p : Path d) → Path (At p) → Path d
  | _, .here, q => q
  | _, .left p, q => .left (Path.append p q)
  | _, .right p, q => .right (Path.append p q)
  | _, .index i p, q => .index i (Path.append p q)

/-- Appending the root path changes nothing. -/
@[simp] theorem append_here {d : Layout} (q : Path d) :
    Path.append (Path.here : Path d) q = q := rfl

/-- Appending from a struct's left component lands in the left component. -/
theorem append_left {a b : Layout} (p : Path a) (q : Path (At p)) :
    Path.append (.left p : Path (.struct a b)) q = .left (Path.append p q) := rfl

/-- Appending from a struct's right component lands in the right component. -/
theorem append_right {a b : Layout} (p : Path b) (q : Path (At p)) :
    Path.append (.right p : Path (.struct a b)) q = .right (Path.append p q) := rfl

/-- Appending from an array's element path stays inside that element. -/
theorem append_index {a : Layout} (i : Nat) (p : Path a) (q : Path (At p)) :
    Path.append (.index i p) q = .index i (Path.append p q) := rfl

/-- Two paths into the same layout are disjoint when neither goes through the
other: `q` is not `p` extended by anything, and `p` is not `q` extended by
anything. This excludes the equal paths and every ancestor/descendant pair,
including two paths through the same array index. -/
def Disjoint {d : Layout} (p q : Path d) : Prop :=
  (∀ r : Path (At p), q ≠ Path.append p r) ∧ (∀ r : Path (At q), p ≠ Path.append q r)

/-- Nothing is disjoint from the root path, so a write at the root reaches every
path of the layout. -/
theorem not_disjoint_here_left {d : Layout} (p : Path d) :
    ¬ Disjoint (Path.here : Path d) p :=
  fun h => h.1 p rfl

/-- As `not_disjoint_here_left`, on the other side. -/
theorem not_disjoint_here_right {d : Layout} (p : Path d) :
    ¬ Disjoint p (Path.here : Path d) :=
  fun h => h.2 p rfl

/-- Disjointness of two paths into a struct's left component is disjointness of
the components. -/
theorem disjoint_left_iff {a b : Layout} {p q : Path a} :
    Disjoint (.left p : Path (.struct a b)) (.left q) ↔ Disjoint p q := by
  constructor
  · intro hd
    refine ⟨fun r hr => hd.1 r ?_, fun r hr => hd.2 r ?_⟩
    · rw [hr]; exact (append_left p r).symm
    · rw [hr]; exact (append_left q r).symm
  · intro hd
    refine ⟨fun r hr => hd.1 r ?_, fun r hr => hd.2 r ?_⟩ <;> exact Path.left.inj hr

/-- Disjointness of two paths into a struct's right component is disjointness of
the components. -/
theorem disjoint_right_iff {a b : Layout} {p q : Path b} :
    Disjoint (.right p : Path (.struct a b)) (.right q) ↔ Disjoint p q := by
  constructor
  · intro hd
    refine ⟨fun r hr => hd.1 r ?_, fun r hr => hd.2 r ?_⟩
    · rw [hr]; exact (append_right p r).symm
    · rw [hr]; exact (append_right q r).symm
  · intro hd
    refine ⟨fun r hr => hd.1 r ?_, fun r hr => hd.2 r ?_⟩ <;> exact Path.right.inj hr

/-- Disjointness of two paths into the same array element is disjointness of the
element paths. -/
theorem disjoint_index_iff {a : Layout} {p q : Path a} (i : Nat) :
    Disjoint (.index i p : Path (.arr a)) (.index i q) ↔ Disjoint p q := by
  constructor
  · intro hd
    refine ⟨fun r hr => hd.1 r ?_, fun r hr => hd.2 r ?_⟩
    · rw [hr]; exact (append_index i p r).symm
    · rw [hr]; exact (append_index i q r).symm
  · intro hd
    refine ⟨fun r hr => hd.1 r ?_, fun r hr => hd.2 r ?_⟩ <;> exact (Path.index.inj hr).2

/-- Two paths that go into the left and the right component of a struct are
disjoint. -/
theorem disjoint_left_right {a b : Layout} (p : Path a) (q : Path b) :
    Disjoint (.left p : Path (.struct a b)) (.right q) := by
  constructor <;> intro r hr <;> cases hr

/-- Two paths that go into the right and the left component of a struct are
disjoint. -/
theorem disjoint_right_left {a b : Layout} (p : Path b) (q : Path a) :
    Disjoint (.right p : Path (.struct a b)) (.left q) := by
  constructor <;> intro r hr <;> cases hr

/-- Two paths into different array elements are disjoint, including when the
element paths themselves address the same shape: the two indices already make
the paths differ. -/
theorem disjoint_index_ne {a : Layout} {p q : Path a} {i j : Nat} (h : i ≠ j) :
    Disjoint (.index i p : Path (.arr a)) (.index j q) :=
  ⟨fun _ hr => h (Path.index.inj hr).1.symm, fun _ hr => h (Path.index.inj hr).1⟩

/-! ## The default state and the owned exchange

`obsDefault` and `stateDefault` are the placeholder an array holds at the slot a
take-out emptied: a leaf's default observation, a pair of defaults, the empty
array. `takeOut` is the take-out itself, an owned exchange (`Array.swapAt`) that
puts the placeholder in the slot and hands the element back, so the array keeps
its size and every other slot. It is internal: the public read and write are
`read?` and `setLeaf`, and `takeOut` and `plugAt` are not exported, because they
hand back the raw element an update below the slot works on. `plugAt` is the
inverse exchange, and it is what puts a focus back — and what undoes a take-out
when the path below it cannot be opened. -/

section ArrayLemmas

variable {α : Type}

/-- The element an owned exchange takes out. -/
private theorem swapAt_fst (s : Array α) (i : Nat) (w : α) (h : i < s.size) :
    (s.swapAt i w h).1 = s[i] := rfl

/-- The array an owned exchange leaves: the original with `w` at the slot. -/
private theorem swapAt_snd (s : Array α) (i : Nat) (w : α) (h : i < s.size) :
    (s.swapAt i w h).2 = s.set i w h := rfl

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

/-- The array a take-out leaves: the original with the placeholder at the slot. -/
@[simp] private theorem takeOut_fst (s : Array α) (i : Nat) (h : i < s.size) (d : α) :
    (takeOut s i h d).1 = s.set i d h := rfl

/-- The element a take-out extracted. -/
@[simp] private theorem takeOut_snd (s : Array α) (i : Nat) (h : i < s.size) (d : α) :
    (takeOut s i h d).2 = s[i] := rfl

/-- A take-out keeps the array's size, so the index it used is still in
bounds. -/
private theorem takeOut_bound (s : Array α) (i : Nat) (h : i < s.size) (d : α) :
    i < (takeOut s i h d).1.size := by
  rw [takeOut_fst, Array.size_set]
  exact h

/-- The array a take-out left, read off the equation that named the pair it
returned. -/
private theorem takeOut_fst_of_eq {s : Array α} {i : Nat} {h : i < s.size} {d : α}
    {sib : Array α} {focus : α} (hp : takeOut s i h d = (sib, focus)) :
    sib = s.set i d h := by
  cases hp
  exact takeOut_fst s i h d

/-- The element a take-out extracted, read off the equation that named the pair
it returned. -/
private theorem takeOut_snd_of_eq {s : Array α} {i : Nat} {h : i < s.size} {d : α}
    {sib : Array α} {focus : α} (hp : takeOut s i h d = (sib, focus)) :
    focus = s[i] := by
  cases hp
  exact takeOut_snd s i h d

/-- The bound a take-out leaves for its index, read off the equation that named
the pair it returned: the siblings array still has the index. -/
private theorem takeOut_bound_of_eq {s : Array α} {i : Nat} {h : i < s.size} {d : α}
    {sib : Array α} {focus : α} (hp : takeOut s i h d = (sib, focus)) : i < sib.size := by
  rw [takeOut_fst_of_eq hp, Array.size_set]
  exact h

/-- A take-out with the size evidence its put-back needs: the array, the
element, and that the index is still in bounds for the array. The fused update
matches on this so that the evidence is a match variable rather than a proof
term whose type mentions the take-out. -/
private def takeOutAt (s : Array α) (i : Nat) (h : i < s.size) (d : α) :
    { p : Array α × α // i < p.1.size } :=
  ⟨takeOut s i h d, takeOut_bound s i h d⟩

/-- The bound-carrying take-out at the pair a plain take-out returned. -/
private theorem takeOutAt_of_eq {s : Array α} {i : Nat} {h : i < s.size} {d : α}
    {sib : Array α} {focus : α} (htk : takeOut s i h d = (sib, focus)) :
    takeOutAt s i h d = ⟨(sib, focus), takeOut_bound_of_eq htk⟩ :=
  Subtype.ext htk

/-- The array check is the identity in the logic: the checked array is the
array, so a proof about a take-out may read the equation with the check
removed. -/
private theorem assertExclusiveArray_self {α : Type} (site : String) (a : Array α) :
    assertExclusiveArray site a = a := rfl

/-- A take-out leaves the placeholder at its slot. -/
private theorem takeOut_getElem?_self (s : Array α) (i : Nat) {h : i < s.size} (d : α) :
    (takeOut s i h d).1[i]? = some d := by
  rw [takeOut_fst]
  simp

/-- A take-out leaves every other slot alone. -/
private theorem takeOut_getElem?_ne (s : Array α) (i : Nat) {h : i < s.size} (d : α) {j : Nat}
    (hji : j ≠ i) : (takeOut s i h d).1[j]? = s[j]? := by
  rw [takeOut_fst, Array.getElem?_set]
  rw [ite_eq_right (Ne.symm hji)]

/-- Put a focus back where a take-out emptied a slot: the exchange in the other
direction, which drops the placeholder the array holds and installs the focus.
As with the take-out, it is in place when the array is exclusively owned, whose
exclusivity is again the caller's to check. -/
private def plugAt (sib : Array α) (i : Nat) (h : i < sib.size) (w : α) : Array α :=
  (sib.swapAt i w h).2

/-- A put-back keeps the array's size. -/
@[simp] private theorem plugAt_size (sib : Array α) (i : Nat) {h : i < sib.size} (w : α) :
    (plugAt sib i h w).size = sib.size := by
  rw [plugAt, swapAt_snd, Array.size_set]

/-- The focus lands at its slot. -/
private theorem plugAt_getElem?_self (sib : Array α) (i : Nat) {h : i < sib.size} (w : α) :
    (plugAt sib i h w)[i]? = some w := by
  rw [plugAt, swapAt_snd]
  simp

/-- Every other slot is left alone. -/
private theorem plugAt_getElem?_ne (sib : Array α) (i : Nat) {h : i < sib.size} (w : α) {j : Nat}
    (hji : j ≠ i) : (plugAt sib i h w)[j]? = sib[j]? := by
  rw [plugAt, swapAt_snd, Array.getElem?_set]
  rw [ite_eq_right (Ne.symm hji)]

/-- The take-out/put-back round trip: putting the element a take-out extracted
back at the slot it emptied gives the array the take-out started from. This is
also the undo a failed path below the take-out needs. -/
private theorem plugAt_takeOut (s : Array α) (i : Nat) (h : i < s.size) (d : α)
    {hh : i < (takeOut s i h d).1.size} :
    plugAt (takeOut s i h d).1 i hh (takeOut s i h d).2 = s := by
  apply Array.ext_getElem?
  intro j
  by_cases hji : j = i
  · rw [hji, plugAt_getElem?_self, takeOut_snd, Array.getElem?_eq_getElem h]
  · rw [plugAt_getElem?_ne _ i _ hji, takeOut_getElem?_ne s i d hji]

/-- The take-out/put-back round trip, read off the equation that names the pair
the take-out returned: what a take-out handed back puts the array back the way
it was. This is also the undo a failed path below the take-out needs. -/
private theorem plugAt_takeOut_of_eq {s : Array α} {i : Nat} {h : i < s.size} {d : α}
    {sib : Array α} {focus : α} (hp : takeOut s i h d = (sib, focus))
    {hb : i < sib.size} : plugAt sib i hb focus = s := by
  cases hp
  exact plugAt_takeOut s i h d

end ArrayLemmas

/-! ## The placeholder of a layout

The default state of a layout is what a take-out leaves in the slot it emptied:
a leaf's default observation, a pair of the components' defaults, and the empty
array. It is a value of the state type, not an `Inhabited` instance, so it does
not become the implicit default of any other definition. -/

/-- The default observation of a description. -/
def obsDefault : (o : ObsDesc) → ObsEl o
  | .unit => ()
  | .nat => 0
  | .uint => 0
  | .bool => false
  | .sum a _ => .inl (obsDefault a)
  | .option _ => none
  | .pair a b => (obsDefault a, obsDefault b)

/-- The default state of a layout. -/
def stateDefault : (a : Layout) → State a
  | .leaf o => obsDefault o
  | .struct a b => (stateDefault a, stateDefault b)
  | .arr _ => #[]

/-! ## The encoding of a leaf observation

`encodeObs` is the library's one route from an observation element to a `Value`,
and it never produces a `.loc`: every observation of the closed universe is
immutable data. -/

/-- Encode a leaf observation as a logical value. Unit, natural, word and
boolean use the corresponding `Value` constructor; sum, option and pair recurse,
so a `.loc` can never appear. -/
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

/-- `encodeObs` distinguishes observations of one description: two elements it
encodes as the same value are the same element. The proof is a structural
induction with one case per constructor, the sum, option and pair cases
descending into both components. -/
theorem encodeObs_injective : ∀ (o : ObsDesc) (x y : ObsEl o),
    encodeObs o x = encodeObs o y → x = y
  | .unit, x, y, _ => by cases x; cases y; rfl
  | .nat, _, _, h => Value.nat.inj h
  | .uint, _, _, h => Value.uint.inj h
  | .bool, _, _, h => Value.bool.inj h
  | .sum a b, x, y, h => by
      cases x with
      | inl x' =>
        cases y with
        | inl y' => exact congrArg Sum.inl (encodeObs_injective a x' y' (Value.inl.inj h))
        | inr y' => exact absurd h (by simp [encodeObs])
      | inr x' =>
        cases y with
        | inl y' => exact absurd h (by simp [encodeObs])
        | inr y' => exact congrArg Sum.inr (encodeObs_injective b x' y' (Value.inr.inj h))
  | .option a, x, y, h => by
      cases x with
      | none =>
        cases y with
        | none => rfl
        | some y' => exact absurd h (by simp [encodeObs])
      | some x' =>
        cases y with
        | none => exact absurd h (by simp [encodeObs])
        | some y' => exact congrArg some (encodeObs_injective a x' y' (Value.some.inj h))
  | .pair a b, x, y, h => by
      obtain ⟨x1, x2⟩ := x
      obtain ⟨y1, y2⟩ := y
      simp only [encodeObs] at h
      have h1 : encodeObs a x1 = encodeObs a y1 := (Value.pair.inj h).1
      have h2 : encodeObs b x2 = encodeObs b y2 := (Value.pair.inj h).2
      rw [encodeObs_injective a x1 y1 h1, encodeObs_injective b x2 y2 h2]

/-- An observation of any description is detached from every root: the encoding
never produces a `.loc`, so it names no root. The proof is a structural
induction with one case per constructor. -/
theorem encodeObs_noRef (ℓ : Loc) : ∀ (o : ObsDesc) (x : ObsEl o),
    NoRef ℓ (encodeObs o x)
  | .unit, x => by cases x; trivial
  | .nat, _ => trivial
  | .uint, _ => trivial
  | .bool, _ => trivial
  | .sum a _, Sum.inl x => encodeObs_noRef ℓ a x
  | .sum _ b, Sum.inr y => encodeObs_noRef ℓ b y
  | .option _, none => trivial
  | .option a, some x => encodeObs_noRef ℓ a x
  | .pair a b, (x, y) => ⟨encodeObs_noRef ℓ a x, encodeObs_noRef ℓ b y⟩

/-! ## The zipper

A `Context d p` is the one-hole context of a path: everything of the state that
is not the focus, with the focus's position recorded. The array context holds
the array the take-out left — the original with the layout's placeholder at the
focus's index — and that index, so `plug` can put a focus back exactly where the
old one was.

`open` reports an out-of-bounds index at any depth by `.error s` with the
original state, so a failed write leaves the state logically unchanged: the
take-out is undone by putting the reported state back before reporting failure.
The zipper is the write's *specification*: `plug_update` says a successful
`setLeaf` is `plug` of the context `open` reported plugged with the new
observation, and `setLeaf` itself is the fused recursion of the next section,
proved equal to it. -/

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

/-- Fill a one-hole context with a focus: the state the context describes, with
the focus in its place. -/
private def plug : {d : Layout} → {p : Path d} → Context d p → State (At p) → State d
  | _, _, .here _, x => x
  | _, _, .left inner right, x => (plug inner x, right)
  | _, _, .right left inner, x => (left, plug inner x)
  | _, _, .index i siblings bound inner, x =>
      plugAt siblings i bound (plug inner x)

/-- `plug` at the root context: the focus is the state. -/
@[simp] private theorem plug_here {d : Layout} (x : State d) : plug (.here d) x = x := rfl

/-- `plug` at a struct's left context. -/
private theorem plug_left {a b : Layout} {p : Path a} (inner : Context a p) (right : State b)
    (x : State (At p)) :
    plug (.left inner right : Context (.struct a b) (.left p)) x = (plug inner x, right) := rfl

/-- `plug` at a struct's right context. -/
private theorem plug_right {a b : Layout} {p : Path b} (left : State a) (inner : Context b p)
    (x : State (At p)) :
    plug (.right left inner : Context (.struct a b) (.right p)) x = (left, plug inner x) := rfl

/-- `plug` at an array context: the inner focus is plugged and put back at the
index the take-out recorded. -/
private theorem plug_index {a : Layout} {p : Path a} (i : Nat) (siblings : Array (State a))
    (bound : i < siblings.size) (inner : Context a p) (x : State (At p)) :
    plug (.index i siblings bound inner : Context (.arr a) (.index i p)) x =
      plugAt siblings i bound (plug inner x) := rfl

/-- The report site of a take-out array mutation. -/
def openSite : String := "Scidonia.FracPerm.StateVar.Layout5.open"

/-- The report site of an extracted element that is about to be written: the
check on the focus, beside the check on the array the take-out emptied. -/
def structSite : String := "Scidonia.FracPerm.StateVar.Layout5.struct"

/-- Take a state apart at a path: the context and the focus, or the unchanged
state when the path does not address anything (an out-of-bounds index at any
depth). The selected element is taken out of its array *before* the path is
followed into it — an owned exchange that leaves the layout's placeholder in the
emptied slot, its result destructured so the extracted element is named once —
and the focus is then checked on its own: the array's exclusivity is not the
element's, because another slot may point at the same object. The two checks
guard the array the take-out emptied and the element it extracted; both are the
identity in the logic, so no theorem mentions them. A failure after the take-out
puts the state the inner `open` reported back — the element it was given, by
`open_failed` — so the reported state is the original one. -/
private def «open» : {d : Layout} → (p : Path d) → State d →
    Except (State d) (Context d p × State (At p))
  | _, .here, s => .ok (.here _, s)
  | _, .left p, s =>
    match «open» p s.1 with
    | .ok (c, x) => .ok (.left c s.2, x)
    | .error _ => .error s
  | _, .right p, s =>
    match «open» p s.2 with
    | .ok (c, x) => .ok (.right s.1 c, x)
    | .error _ => .error s
  | _, .index i p, s =>
    if h : i < s.size then
      match hr : takeOut (assertExclusiveArray openSite s) i h (stateDefault _) with
      | (sib, focus) =>
        match «open» p (assertExclusive structSite focus) with
        | .ok (c, x) => .ok (.index i sib (takeOut_bound_of_eq hr) c, x)
        | .error e => .error (plugAt sib i (takeOut_bound_of_eq hr) e)
    else .error s

/-- `open` at the root path: the whole state is the focus. -/
@[simp] private theorem open_here {d : Layout} (s : State d) :
    «open» (Path.here : Path d) s = .ok (.here d, s) := rfl

/-- `open` at a struct's left component: the inner path is opened on the left
component and the right one is held. -/
private theorem open_left {a b : Layout} (p : Path a) (s : State (.struct a b)) :
    «open» (.left p) s =
      (match «open» p s.1 with
       | .ok (c, x) => .ok (.left c s.2, x)
       | .error _ => .error s) := rfl

/-- `open` at a struct's right component. -/
private theorem open_right {a b : Layout} (p : Path b) (s : State (.struct a b)) :
    «open» (.right p) s =
      (match «open» p s.2 with
       | .ok (c, x) => .ok (.right s.1 c, x)
       | .error _ => .error s) := rfl

/-- `open` at an array element, with the take-out and its two checks written
out: the checked array is taken apart into the placeholder-holding siblings
array and the extracted element, the pair is destructured so the element is
named once, and the extracted element is checked on its own before the inner
path is opened on it — the array's exclusivity does not make the element unique,
since another slot may alias it. A failure after the take-out puts the state the
inner `open` reported back — the element it was given — so the take-out is
undone. -/
private theorem open_index {a : Layout} (i : Nat) (p : Path a) (s : Array (State a)) :
    «open» (.index i p) s =
      (if h : i < s.size then
        (match hr : takeOut (assertExclusiveArray openSite s) i h (stateDefault _) with
         | (sib, focus) =>
           match «open» p (assertExclusive structSite focus) with
           | .ok (c, x) => .ok (.index i sib (takeOut_bound_of_eq hr) c, x)
           | .error e => .error (plugAt sib i (takeOut_bound_of_eq hr) e))
       else .error s) := rfl

/-! ## Reading and writing a leaf

`leafAt?` is the private traversal: it is the only place a raw focus is
obtained, and it is not exported. `read?` maps it through `encodeObs`
immediately, so its result is a `Value` of the observation universe and never a
state or a subtree. -/

/-- The raw focus at a leaf path, as an observation element. Private: this is
the traversal whose result is immediately encoded by `read?`. -/
private def leafAt? : {d : Layout} → (p : Path d) → (o : ObsDesc) →
    (h : At p = .leaf o) → State d → Option (ObsEl o)
  | _, .here, _, h, s => some (cast (congrArg State h) s)
  | _, .left p, o, h, s => leafAt? p o h s.1
  | _, .right p, o, h, s => leafAt? p o h s.2
  | _, .index i p, o, h, s =>
    match s[i]? with
    | some e => leafAt? p o h e
    | none => none

/-- Read a leaf path: the library's encoding of the observation at the path's
end, or `none` when the path does not address anything. The result is an
immutable `Value`; there is no route from here to the state or a subtree. -/
def read? {d : Layout} (p : ObsPath d) (s : State d) : Option Value :=
  (leafAt? p.path p.obs p.leaf s).map (encodeObs p.obs)

/-! ## Validity and the fused update

`setLeaf` asks first whether the path addresses anything — `inBounds` walks the
path and reads the arrays without copying them — and only then runs the update,
which returns the state alone and threads the new focus through the recursion as
a value rather than as a function of the old state, so the write path allocates
no closure. Keeping the pair out of the recursion is what lets the compiler
reuse a struct cell for the struct it rebuilds: the struct case of `setAt` is
`let (a, b) := s; (setAt q y a, b)`, whose result has the shape of the cell it
came from. `setAt` is total; on a path `inBounds` accepts it always reaches the
leaf, and its array case takes the selected element out, checks the extracted
focus, recurses on it and puts it back. The zipper above is the specification,
and the next section proves `setLeaf` equal to its path replacement, so the
theorems stated through `setLeaf` are unchanged. -/

/-- Whether every index along a path is in bounds. A pure traversal: it reads
an array's element and never copies the array. -/
private def inBounds : {d : Layout} → (p : Path d) → State d → Bool
  | _, .here, _ => true
  | _, .left q, s => inBounds q s.1
  | _, .right q, s => inBounds q s.2
  | _, .index i q, s => if h : i < s.size then inBounds q s[i] else false

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

/-- `inBounds` at the root path: the root addresses the state. -/
@[simp] private theorem inBounds_here {d : Layout} (s : State d) :
    inBounds (Path.here : Path d) s = true := rfl

/-- `inBounds` at a struct's left component. -/
private theorem inBounds_left {a b : Layout} (q : Path a) (s : State (.struct a b)) :
    inBounds (.left q) s = inBounds q s.1 := rfl

/-- `inBounds` at a struct's right component. -/
private theorem inBounds_right {a b : Layout} (q : Path b) (s : State (.struct a b)) :
    inBounds (.right q) s = inBounds q s.2 := rfl

/-- `inBounds` at an array element: the element at the index, read without
copying the array. -/
private theorem inBounds_index {a : Layout} (i : Nat) (q : Path a) (s : Array (State a)) :
    inBounds (.index i q) s =
      (if h : i < s.size then inBounds q s[i] else false) := rfl

/-- `setAt` at the root path: the new focus is the state. -/
@[simp] private theorem setAt_here {d : Layout} (y : State (At (Path.here : Path d)))
    (s : State d) :
    setAt (Path.here : Path d) y s = y := rfl

/-- `setAt` at a struct's left component: the pair is destructured and the
updated component is put back in it. -/
private theorem setAt_left {a b : Layout} (q : Path a) (y : State (At q))
    (u : State a) (v : State b) :
    setAt (.left q) y (u, v) = (setAt q y u, v) := rfl

/-- `setAt` at a struct's right component. -/
private theorem setAt_right {a b : Layout} (q : Path b) (y : State (At q))
    (u : State a) (v : State b) :
    setAt (.right q) y (u, v) = (u, setAt q y v) := rfl

/-- `setAt` at an array element: the take-out, the focus check, the recursion
and the put-back, written out. -/
private theorem setAt_index {a : Layout} (i : Nat) (q : Path a)
    (y : State (At q)) (s : Array (State a)) :
    setAt (.index i q) y s =
      (if h : i < s.size then
        (match takeOutAt (assertExclusiveArray openSite s) i h (stateDefault _) with
         | ⟨(sib, focus), hbound⟩ =>
           plugAt sib i hbound (setAt q y (assertExclusive structSite focus)))
       else s) := rfl

/-- Replace the leaf a path addresses: the state with the path's focus set to
the new observation, and whether the write took effect (`false` for an
out-of-bounds index, in which case the state is unchanged). `inBounds` decides
first, so the fused update runs only on a path that addresses something; each
struct cell is then rebuilt from its updated component, and an array element is
taken out, checked, updated and put back. The new focus is cast once, here, and
threaded through the update as a value. -/
def setLeaf {d : Layout} (p : ObsPath d) (x : ObsEl p.obs) (s : State d) :
    State d × Bool :=
  if inBounds p.path s then
    (setAt p.path (cast (congrArg State p.leaf.symm) x) s, true)
  else (s, false)

/-! ## The zipper's round trip

`open` and `plug` are inverse in the sense a one-hole context promises: plugging
a state the context came from gives the state back, plugging the focus a write
produced gives exactly the path replacement, and a failed `open` leaves the
state it was given. -/

/-- Filling a one-hole context with a state the context came from gives the
state back. -/
private theorem open_plug {d : Layout} (p : Path d) (s : State d) (c : Context d p)
    (x : State (At p)) (h : «open» p s = .ok (c, x)) : plug c x = s := by
  induction p with
  | here =>
    cases c
    rw [open_here] at h
    cases h
    rfl
  | left p ih =>
    cases c with
    | left inner right =>
      rw [open_left] at h
      cases h' : «open» p s.1 with
      | ok v =>
        simp only [h'] at h
        cases h
        rw [plug_left]
        rw [ih (s := s.1) (c := v.1) (x := v.2) h']
      | error e => simp only [h'] at h; simp at h
  | right p ih =>
    cases c with
    | right left inner =>
      rw [open_right] at h
      cases h' : «open» p s.2 with
      | ok v =>
        simp only [h'] at h
        cases h
        rw [plug_right]
        rw [ih (s := s.2) (c := v.1) (x := v.2) h']
      | error e => simp only [h'] at h; simp at h
  | index i p ih =>
    cases c with
    | index i' siblings bound inner =>
      rw [open_index] at h
      split at h
      · rename_i hlt
        simp only [assertExclusiveArray_self] at h
        cases hr : takeOut s i hlt (stateDefault _) with
        | mk sib focus =>
          cases h' : «open» p (assertExclusive structSite focus) with
          | ok v =>
            simp only [hr, h'] at h
            have hx : x = v.2 := (Prod.mk.inj (Except.ok.inj h)).2.symm
            rw [← (Prod.mk.inj (Except.ok.inj h)).1, hx]
            rw [show plug (Context.index i sib (takeOut_bound_of_eq hr) v.1) v.2 =
                  plugAt sib i (takeOut_bound_of_eq hr) (plug v.1 v.2) from rfl]
            rw [ih (s := assertExclusive structSite focus) (c := v.1) (x := v.2) h']
            exact plugAt_takeOut_of_eq hr
          | error e => simp only [hr, h'] at h; simp at h
      · simp at h

/-- A failed `open` leaves the state it was given: an out-of-bounds index at any
depth reports the original state, so a failed write changes nothing. -/
private theorem open_failed {d : Layout} (p : Path d) (s old : State d)
    (h : «open» p s = .error old) : old = s := by
  induction p with
  | here => rw [open_here] at h; simp at h
  | left p ih =>
    rw [open_left] at h
    split at h
    · simp at h
    · simpa only [Except.error.injEq] using h.symm
  | right p ih =>
    rw [open_right] at h
    split at h
    · simp at h
    · simpa only [Except.error.injEq] using h.symm
  | index i p ih =>
    rw [open_index] at h
    split at h
    · rename_i hlt
      simp only [assertExclusiveArray_self] at h
      cases hr : takeOut s i hlt (stateDefault _) with
      | mk sib focus =>
        cases h' : «open» p (assertExclusive structSite focus) with
        | ok v => simp only [hr, h'] at h; simp at h
        | error e =>
          simp only [hr, h', Except.error.injEq] at h
          refine h.symm.trans ?_
          rw [ih (assertExclusive structSite focus) e h']
          exact plugAt_takeOut_of_eq hr
    · simpa only [Except.error.injEq] using h.symm

/-- A successful `open` means every index along the path is in bounds. -/
private theorem open_inBounds : ∀ {d : Layout} (p : Path d) (s : State d)
    (c : Context d p) (f : State (At p)), «open» p s = .ok (c, f) → inBounds p s = true := by
  intro d p
  induction p with
  | here =>
    intro s c f hopen
    rw [open_here] at hopen
    rfl
  | left q ih =>
    intro s c f hopen
    obtain ⟨u, v⟩ := s
    rw [open_left] at hopen
    cases hq : «open» q u with
    | ok w => simp only [hq] at hopen; rw [inBounds_left]; exact ih u w.1 w.2 hq
    | error e => simp only [hq] at hopen; simp at hopen
  | right q ih =>
    intro s c f hopen
    obtain ⟨u, v⟩ := s
    rw [open_right] at hopen
    cases hq : «open» q v with
    | ok w => simp only [hq] at hopen; rw [inBounds_right]; exact ih v w.1 w.2 hq
    | error e => simp only [hq] at hopen; simp at hopen
  | index i q ih =>
    intro s c f hopen
    rw [open_index] at hopen
    by_cases hb : i < s.size
    · rw [dite_eq_left hb] at hopen
      simp only [assertExclusiveArray_self] at hopen
      rw [inBounds_index, dite_eq_left hb]
      cases hr : takeOut s i hb (stateDefault _) with
      | mk sib focus =>
        cases hq : «open» q (assertExclusive structSite focus) with
        | ok w =>
          rw [← takeOut_snd_of_eq hr]
          exact ih (assertExclusive structSite focus) w.1 w.2 hq
        | error e => simp only [hr, hq] at hopen; simp at hopen
    · rw [dite_eq_right hb] at hopen
      simp at hopen

/-- A failing `open` means some index along the path is out of bounds. -/
private theorem open_error_notInBounds : ∀ {d : Layout} (p : Path d) (s old : State d),
    «open» p s = .error old → inBounds p s = false := by
  intro d p
  induction p with
  | here => intro s old h; rw [open_here] at h; simp at h
  | left q ih =>
    intro s old h
    obtain ⟨u, v⟩ := s
    rw [open_left] at h
    cases hq : «open» q u with
    | ok w => simp only [hq] at h; simp at h
    | error e => simp only [hq] at h; rw [inBounds_left]; exact ih u e hq
  | right q ih =>
    intro s old h
    obtain ⟨u, v⟩ := s
    rw [open_right] at h
    cases hq : «open» q v with
    | ok w => simp only [hq] at h; simp at h
    | error e => simp only [hq] at h; rw [inBounds_right]; exact ih v e hq
  | index i q ih =>
    intro s old h
    rw [open_index] at h
    by_cases hb : i < s.size
    · rw [dite_eq_left hb] at h
      simp only [assertExclusiveArray_self] at h
      rw [inBounds_index, dite_eq_left hb]
      cases hr : takeOut s i hb (stateDefault _) with
      | mk sib focus =>
        cases hq : «open» q (assertExclusive structSite focus) with
        | ok w => simp only [hr, hq] at h; simp at h
        | error e =>
          rw [← takeOut_snd_of_eq hr]
          exact ih (assertExclusive structSite focus) e hq
    · rw [dite_eq_right hb] at h
      rw [inBounds_index, dite_eq_right hb]

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
    rw [open_here] at hopen
    obtain ⟨hc, _⟩ := Prod.mk.inj (Except.ok.inj hopen)
    rw [← hc]
    rfl
  | left q ih =>
    intro s c f y hopen
    obtain ⟨u, v⟩ := s
    rw [open_left] at hopen
    cases hq : «open» q u with
    | ok w =>
      simp only [hq] at hopen
      obtain ⟨hc, _⟩ := Prod.mk.inj (Except.ok.inj hopen)
      rw [← hc, setAt_left, ih u w.1 w.2 y hq, plug_left]
    | error e => simp only [hq] at hopen; simp at hopen
  | right q ih =>
    intro s c f y hopen
    obtain ⟨u, v⟩ := s
    rw [open_right] at hopen
    cases hq : «open» q v with
    | ok w =>
      simp only [hq] at hopen
      obtain ⟨hc, _⟩ := Prod.mk.inj (Except.ok.inj hopen)
      rw [← hc, setAt_right, ih v w.1 w.2 y hq, plug_right]
    | error e => simp only [hq] at hopen; simp at hopen
  | index i q ih =>
    intro s c f y hopen
    rw [open_index] at hopen
    by_cases hb : i < s.size
    · rw [dite_eq_left hb] at hopen
      rw [setAt_index, dite_eq_left hb]
      cases hr : takeOut (assertExclusiveArray openSite s) i hb (stateDefault _) with
      | mk sib focus =>
        rw [takeOutAt_of_eq hr]
        simp only []
        cases hq : «open» q (assertExclusive structSite focus) with
        | ok w =>
          simp only [hr, hq] at hopen
          obtain ⟨hc, _⟩ := Prod.mk.inj (Except.ok.inj hopen)
          rw [← hc, plug_index, ih (assertExclusive structSite focus) w.1 w.2 y hq]
        | error e => simp only [hr, hq] at hopen; simp at hopen
    · rw [dite_eq_right hb] at hopen
      simp at hopen

/-- A successful `setLeaf` is exactly the path replacement: the state is the
context the old state opened to, plugged with the new observation. -/
private theorem plug_update {d : Layout} (p : ObsPath d) (s : State d) (c : Context d p.path)
    (old : State (At p.path)) (new : ObsEl p.obs)
    (h : «open» p.path s = .ok (c, old)) :
    setLeaf p new s = (plug c (cast (congrArg State p.leaf.symm) new), true) := by
  have hib := open_inBounds p.path s c old h
  rw [setLeaf, hib]
  rw [setAt_spec p.path s c old (cast (congrArg State p.leaf.symm) new) h]
  exact rfl

/-- A failing `setLeaf` is the state `open` reported, with the write reported as
not taking effect. -/
private theorem setLeaf_error {d : Layout} (p : ObsPath d) (x : ObsEl p.obs)
    (s old : State d) (h : «open» p.path s = .error old) :
    setLeaf p x s = (old, false) := by
  have hnib := open_error_notInBounds p.path s old h
  rw [setLeaf, hnib, open_failed p.path s old h]
  exact rfl

/-- A `setLeaf` that reports failure leaves the state alone. -/
theorem setLeaf_failed {d : Layout} (p : ObsPath d) (x : ObsEl p.obs) (s : State d)
    (h : (setLeaf p x s).2 = false) : (setLeaf p x s).1 = s := by
  cases ho : «open» p.path s with
  | ok w =>
    obtain ⟨c, f⟩ := w
    rw [plug_update p s c f x ho] at h
    simp at h
  | error e =>
    rw [setLeaf_error p x s e ho, open_failed p.path s e ho]

/-! ## Reading and writing

`read?` is the public read: it returns the library's encoding of the leaf the
path addresses, never a state. `read?_leafAt?` is the strengthened form: a
successful read names the raw observation and its encoding, which is what
detachment and the snapshot theorems rest on. -/

/-- A successful `read?` names the raw observation at the path and its encoding:
`old` is `encodeObs p.obs x` for the `x` the traversal returned. -/
theorem read?_leafAt? {d : Layout} (p : ObsPath d) (s : State d) (v : Value)
    (h : read? p s = some v) :
    ∃ x : ObsEl p.obs, leafAt? p.path p.obs p.leaf s = some x ∧ v = encodeObs p.obs x := by
  simp only [read?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, hx, rfl⟩

/-- Every read result is detached from every root: `read?` encodes an element of
the observation universe, which names no `.loc`. -/
theorem read_detached {d : Layout} (p : ObsPath d) (s : State d) (v : Value)
    (h : read? p s = some v) (ℓ : Loc) : NoRef ℓ v := by
  obtain ⟨x, _, rfl⟩ := read?_leafAt? p s v h
  exact encodeObs_noRef ℓ p.obs x

/-- The cast the zipper and the write share: an observation element cast up to a
state and back is the element. -/
theorem cast_state_self {l : Layout} {o : ObsDesc} (h : l = .leaf o) (x : ObsEl o) :
    cast (congrArg State h) (cast (congrArg State h.symm) x) = x := by
  cases h
  rfl

/-- `leafAt?` at the root path: the focus is the whole state, transported to
the leaf's type. -/
private theorem leafAt?_here {d : Layout} (o : ObsDesc)
    (hp : At (Path.here : Path d) = .leaf o) (s : State d) :
    leafAt? (Path.here : Path d) o hp s = some (cast (congrArg State hp) s) := rfl

/-- `leafAt?` at a struct's left component. -/
private theorem leafAt?_left {a b : Layout} (p : Path a) (o : ObsDesc)
    (hp : At (.left p : Path (.struct a b)) = .leaf o) (s : State (.struct a b)) :
    leafAt? (.left p) o hp s = leafAt? p o hp s.1 := rfl

/-- `leafAt?` at a struct's right component. -/
private theorem leafAt?_right {a b : Layout} (p : Path b) (o : ObsDesc)
    (hp : At (.right p : Path (.struct a b)) = .leaf o) (s : State (.struct a b)) :
    leafAt? (.right p) o hp s = leafAt? p o hp s.2 := rfl

/-- `leafAt?` at an array element: the element at the index, or nothing when the
index is out of bounds. -/
private theorem leafAt?_index {a : Layout} (i : Nat) (p : Path a) (o : ObsDesc)
    (hp : At (.index i p : Path (.arr a)) = .leaf o) (s : Array (State a)) :
    leafAt? (.index i p) o hp s =
      (match s[i]? with
       | some e => leafAt? p o hp e
       | none => none) := rfl

/-- Reading back at the path a focus was plugged into returns that focus. -/
private theorem leafAt?_plug_self : ∀ {d : Layout} (p : Path d) (o : ObsDesc)
    (hp : At p = .leaf o) (c : Context d p) (x : State (At p)) (s : State d)
    (f : State (At p)),
    «open» p s = .ok (c, f) →
    leafAt? p o hp (plug c x) = some (cast (congrArg State hp) x) := by
  intro d p
  induction p with
  | here =>
    intro o hp c x s f hopen
    have hc : c = Context.here _ := (Prod.mk.inj (Except.ok.inj hopen)).1.symm
    rw [hc, plug_here, leafAt?_here]
  | left p ih =>
    intro o hp c x s f hopen
    rw [open_left] at hopen
    cases h' : «open» p s.1 with
    | ok v =>
      simp only [h'] at hopen
      have hc : c = Context.left v.1 s.2 := (Prod.mk.inj (Except.ok.inj hopen)).1.symm
      rw [hc, plug_left, leafAt?_left]
      exact ih o hp v.1 x s.1 v.2 h'
    | error e => simp only [h'] at hopen; simp at hopen
  | right p ih =>
    intro o hp c x s f hopen
    rw [open_right] at hopen
    cases h' : «open» p s.2 with
    | ok v =>
      simp only [h'] at hopen
      have hc : c = Context.right s.1 v.1 := (Prod.mk.inj (Except.ok.inj hopen)).1.symm
      rw [hc, plug_right, leafAt?_right]
      exact ih o hp v.1 x s.2 v.2 h'
    | error e => simp only [h'] at hopen; simp at hopen
  | index i p ih =>
    intro o hp c x s f hopen
    rw [open_index] at hopen
    split at hopen
    · rename_i hlt
      simp only [assertExclusiveArray_self] at hopen
      cases hr : takeOut s i hlt (stateDefault _) with
      | mk sib focus =>
        cases h' : «open» p (assertExclusive structSite focus) with
        | ok v =>
          simp only [hr, h'] at hopen
          have hc : c = Context.index i sib (takeOut_bound_of_eq hr) v.1 :=
            (Prod.mk.inj (Except.ok.inj hopen)).1.symm
          rw [hc]
          rw [show plug (Context.index i sib (takeOut_bound_of_eq hr) v.1) x =
                plugAt sib i (takeOut_bound_of_eq hr) (plug v.1 x) from rfl]
          rw [leafAt?_index]
          simp only [plugAt_getElem?_self _ i (plug v.1 x)]
          exact ih o hp v.1 x (assertExclusive structSite focus) v.2 h'
        | error e => simp only [hr, h'] at hopen; simp at hopen
    · simp at hopen

/-- A write at a path disjoint from a read path does not change what the read
returns: the take-out and put-back only rebuild the path's own focus. -/
private theorem leafAt?_plug_of_disjoint : ∀ {d : Layout} (p q : Path d) (o : ObsDesc)
    (hq : At q = .leaf o) (c : Context d p) (y : State (At p)) (s : State d)
    (f : State (At p)),
    «open» p s = .ok (c, f) → Disjoint p q →
    leafAt? q o hq (plug c y) = leafAt? q o hq s := by
  intro d p
  induction p with
  | here =>
    intro q o hq c y s f hopen hd
    exact absurd hd (not_disjoint_here_left q)
  | left p ih =>
    intro q o hq c y s f hopen hd
    cases q with
    | here => exact absurd hd (not_disjoint_here_right _)
    | left q' =>
      rw [open_left] at hopen
      cases h' : «open» p s.1 with
      | ok v =>
        simp only [h'] at hopen
        have hc : c = Context.left v.1 s.2 := (Prod.mk.inj (Except.ok.inj hopen)).1.symm
        rw [hc, plug_left, leafAt?_left]
        exact ih q' o hq v.1 y s.1 v.2 h' (disjoint_left_iff.mp hd)
      | error e => simp only [h'] at hopen; simp at hopen
    | right q' =>
      rw [open_left] at hopen
      cases h' : «open» p s.1 with
      | ok v =>
        simp only [h'] at hopen
        have hc : c = Context.left v.1 s.2 := (Prod.mk.inj (Except.ok.inj hopen)).1.symm
        rw [hc, plug_left, leafAt?_right, leafAt?_right]
      | error e => simp only [h'] at hopen; simp at hopen
  | right p ih =>
    intro q o hq c y s f hopen hd
    cases q with
    | here => exact absurd hd (not_disjoint_here_right _)
    | right q' =>
      rw [open_right] at hopen
      cases h' : «open» p s.2 with
      | ok v =>
        simp only [h'] at hopen
        have hc : c = Context.right s.1 v.1 := (Prod.mk.inj (Except.ok.inj hopen)).1.symm
        rw [hc, plug_right, leafAt?_right]
        exact ih q' o hq v.1 y s.2 v.2 h' (disjoint_right_iff.mp hd)
      | error e => simp only [h'] at hopen; simp at hopen
    | left q' =>
      rw [open_right] at hopen
      cases h' : «open» p s.2 with
      | ok v =>
        simp only [h'] at hopen
        have hc : c = Context.right s.1 v.1 := (Prod.mk.inj (Except.ok.inj hopen)).1.symm
        rw [hc, plug_right, leafAt?_left, leafAt?_left]
      | error e => simp only [h'] at hopen; simp at hopen
  | index i p ih =>
    intro q o hq c y s f hopen hd
    cases q with
    | here => exact absurd hd (not_disjoint_here_right _)
    | index j q' =>
      rw [open_index] at hopen
      split at hopen
      · rename_i hlt
        simp only [assertExclusiveArray_self] at hopen
        cases hr : takeOut s i hlt (stateDefault _) with
        | mk sib focus =>
          cases h' : «open» p (assertExclusive structSite focus) with
          | ok v =>
            simp only [hr, h'] at hopen
            have hc : c = Context.index i sib (takeOut_bound_of_eq hr) v.1 :=
              (Prod.mk.inj (Except.ok.inj hopen)).1.symm
            rw [hc]
            rw [show plug (Context.index i sib (takeOut_bound_of_eq hr) v.1) y =
                  plugAt sib i (takeOut_bound_of_eq hr) (plug v.1 y) from rfl]
            rw [leafAt?_index, leafAt?_index]
            have hself : (plugAt sib i (takeOut_bound_of_eq hr) (plug v.1 y))[i]? =
                some (plug v.1 y) :=
              plugAt_getElem?_self _ i (plug v.1 y)
            have hne : ∀ {k : Nat}, k ≠ i →
                (plugAt sib i (takeOut_bound_of_eq hr) (plug v.1 y))[k]? = s[k]? :=
              fun {k} hk => by
                rw [plugAt_getElem?_ne _ i (plug v.1 y) hk, takeOut_fst_of_eq hr,
                  Array.getElem?_set, ite_eq_right (Ne.symm hk)]
            by_cases hji : j = i
            · rw [hji] at hd ⊢
              rw [hself]
              simp only [Array.getElem?_eq_getElem hlt]
              rw [← takeOut_snd_of_eq hr]
              exact ih q' o hq v.1 y (assertExclusive structSite focus) v.2 h'
                (disjoint_index_iff i |>.mp hd)
            · rw [hne hji]
          | error e => simp only [hr, h'] at hopen; simp at hopen
      · simp at hopen

/-- The snapshot: an earlier read's value is bound to the *old* state — the one
`read? p s` returned — while the read after the write encodes the write's own
operand. The two operands are the two different values, not two occurrences of
one. -/
theorem snapshot_after_setLeaf {d : Layout} (p : ObsPath d) (s s' : State d)
    (old : Value) (new : ObsEl p.obs) (hread : read? p s = some old)
    (hwrite : setLeaf p new s = (s', true)) :
    read? p s = some old ∧ read? p s' = some (encodeObs p.obs new) := by
  refine ⟨hread, ?_⟩
  cases hop : «open» p.path s with
  | ok w =>
    obtain ⟨c, f⟩ := w
    rw [plug_update p s c f new hop] at hwrite
    obtain ⟨rfl, -⟩ := hwrite
    show (leafAt? p.path p.obs p.leaf (plug c (cast (congrArg State p.leaf.symm) new))).map
        (encodeObs p.obs) = some (encodeObs p.obs new)
    rw [leafAt?_plug_self p.path p.obs p.leaf c (cast (congrArg State p.leaf.symm) new) s f hop]
    rw [cast_state_self p.leaf new]
    rfl
  | error e =>
    rw [setLeaf_error p new s e hop] at hwrite
    simp at hwrite

/-- A write at a path disjoint from a read path does not change what the read
returns: `Disjoint` is non-overlap of the whole paths, so this covers a sibling
field and another array index alike. -/
theorem read_frame {d : Layout} (p q : ObsPath d) (s s' : State d) (new : ObsEl p.obs)
    (hdisjoint : Disjoint p.path q.path) (hwrite : setLeaf p new s = (s', true)) :
    read? q s' = read? q s := by
  cases hop : «open» p.path s with
  | ok w =>
    obtain ⟨c, f⟩ := w
    rw [plug_update p s c f new hop] at hwrite
    obtain ⟨rfl, -⟩ := hwrite
    show (leafAt? q.path q.obs q.leaf (plug c (cast (congrArg State p.leaf.symm) new))).map
        (encodeObs q.obs) = (leafAt? q.path q.obs q.leaf s).map (encodeObs q.obs)
    rw [leafAt?_plug_of_disjoint p.path q.path q.obs q.leaf c
      (cast (congrArg State p.leaf.symm) new) s f hop hdisjoint]
  | error e =>
    rw [setLeaf_error p new s e hop] at hwrite
    simp at hwrite

/-- No `ObsPath` addresses a whole array: the end of a here-path at an array is
an array, which is not a leaf of the observation universe. -/
theorem array_root_not_observable (o : ObsDesc) :
    At (Path.here : Path (.arr (.leaf .uint))) ≠ .leaf o := by
  intro h
  cases h

/-! ## The lawful adapter

The layout state variable is a *value* of the existing `LawfulStateVar` class
built from library definitions: its read is `read?`'s traversal, its write is
`setLeaf`, and its encoding is the library's `encodeObs`. An author supplies
neither an encoder nor a read operation, so no instance author can make the
class's laws hold by declining to represent a mutable part of the state — the
adapter's result is an immutable observation option. -/

/-- A layout state wrapped so that typeclass inference is indexed by the layout
itself, and so that the adapter is not the description universe's `Described`. -/
structure DescribedLayout (d : Layout) where
  /-- The wrapped state. -/
  value : State d

/-- A write to a layout state: the read path and the observation to install at
its end. -/
abbrev LayoutWrite (d : Layout) := Σ p : ObsPath d, ObsEl p.obs

/-- M5's lawful adapter: reading a layout state is the library's `read?`, writing
it is `setLeaf`, and the encoding of a read result is `encodeObs` of the
observation the path ended at. Every law is the corresponding library fact
(`encodeObs_injective`, `encodeObs_noRef` and `True` validity). -/
@[instance_reducible] def describedLayoutStateVar (d : Layout) :
    LawfulStateVar (DescribedLayout d) (State d) (ObsPath d) (LayoutWrite d) where
  Result p := Option (ObsEl p.obs)
  initial x := ⟨x⟩
  Valid _ := True
  observe p s := leafAt? p.path p.obs p.leaf s.value
  replace w s :=
    (⟨(setLeaf w.1 w.2 s.value).1⟩, (setLeaf w.1 w.2 s.value).2)
  encodeRead p r := r.elim .none (fun x => .some (encodeObs p.obs x))
  initial_valid _ := trivial
  replace_valid _ _ _ := trivial
  encodeRead_injective := by
    intro p x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y' => simp at h
    | some x' =>
      cases y with
      | none => simp at h
      | some y' =>
        simp only [Option.elim_some] at h
        exact congrArg some (encodeObs_injective p.obs x' y' (Value.some.inj h))
  observe_detached := by
    intro ℓ p s _
    cases h : leafAt? p.path p.obs p.leaf s.value with
    | none => trivial
    | some x => exact encodeObs_noRef ℓ p.obs x

/-- The adapter's read is the library traversal: its result is the leaf the path
addresses, or nothing when the path does not address anything. -/
@[simp] theorem describedLayout_observe_eq (d : Layout) (p : ObsPath d) (s : DescribedLayout d) :
    (describedLayoutStateVar d).observe p s = leafAt? p.path p.obs p.leaf s.value := rfl

/-- The adapter's write is `setLeaf` on the wrapped state. -/
@[simp] theorem describedLayout_replace_eq (d : Layout) (p : ObsPath d) (x : ObsEl p.obs)
    (s : DescribedLayout d) :
    (describedLayoutStateVar d).replace ⟨p, x⟩ s =
      (⟨(setLeaf p x s.value).1⟩, (setLeaf p x s.value).2) := rfl

/-- A failed adapter write leaves the state alone. -/
theorem describedLayout_replace_failed (d : Layout) (p : ObsPath d) (x : ObsEl p.obs)
    (s : DescribedLayout d) (h : (setLeaf p x s.value).2 = false) :
    ((describedLayoutStateVar d).replace ⟨p, x⟩ s).1 = s := by
  show (⟨(setLeaf p x s.value).1⟩ : DescribedLayout d) = s
  rw [setLeaf_failed p x s.value h]

/-- Reading back after a successful adapter write returns the observation that
was written. -/
theorem describedLayout_read_after_replace (d : Layout) (p : ObsPath d)
    (x : ObsEl p.obs) (s : DescribedLayout d) (h : (setLeaf p x s.value).2 = true) :
    (describedLayoutStateVar d).observe p
      ((describedLayoutStateVar d).replace ⟨p, x⟩ s).1 = some x := by
  rw [describedLayout_observe_eq, describedLayout_replace_eq]
  show leafAt? p.path p.obs p.leaf (setLeaf p x s.value).1 = some x
  cases hop : «open» p.path s.value with
  | ok w =>
    obtain ⟨c, f⟩ := w
    rw [plug_update p s.value c f x hop]
    show leafAt? p.path p.obs p.leaf (plug c (cast (congrArg State p.leaf.symm) x)) = some x
    rw [leafAt?_plug_self p.path p.obs p.leaf c (cast (congrArg State p.leaf.symm) x) s.value f hop]
    exact congrArg some (cast_state_self p.leaf x)
  | error e =>
    rw [setLeaf_error p x s.value e hop] at h
    simp at h

/-- The generic model's primitive-detachment law at the adapter. -/
theorem describedLayout_primitive_detached (d : Layout) (ℓ : Loc) (p : ObsPath d)
    (s : DescribedLayout d) :
    NoRef ℓ ((describedLayoutStateVar d).encodeRead p
      ((describedLayoutStateVar d).observe p s)) :=
  primitive_detached (inst := describedLayoutStateVar d) trivial

/-- The generic heap transition at the adapter: what a read of a root holding a
layout state returns is detached from that root. -/
theorem describedLayout_read_at_detached (d : Layout) {ℓ : Loc} {p : ObsPath d}
    {h h' : Heap (DescribedLayout d)} {v : Option (ObsEl p.obs)}
    (hr : ReadAt (describedLayoutStateVar d) ℓ p h h' v) :
    NoRef ℓ ((describedLayoutStateVar d).encodeRead p v) :=
  read_at_detached (inst := describedLayoutStateVar d) hr

/-- The generic heap transition at the adapter: a write leaves an admissible
state in the root cell. -/
theorem describedLayout_write_at_valid (d : Layout) {ℓ : Loc} {w : LayoutWrite d}
    {h h' : Heap (DescribedLayout d)} {b : Bool}
    (hw : WriteAt (describedLayoutStateVar d) ℓ w h h' b) :
    ∃ s', Scidonia.FracPerm.StateVar.At ℓ s' h' ∧ (describedLayoutStateVar d).Valid s' :=
  write_at_valid (inst := describedLayoutStateVar d) hw

/-- The generic heap transition at the adapter: a write changes no other cell. -/
theorem describedLayout_write_at_frame (d : Layout) {ℓ m : Loc} {w : LayoutWrite d}
    {h h' : Heap (DescribedLayout d)} {b : Bool}
    (hw : WriteAt (describedLayoutStateVar d) ℓ w h h' b) (hm : m ≠ ℓ) :
    h' m = h m :=
  write_at_frame (inst := describedLayoutStateVar d) hw hm

end Layout5

end Scidonia.FracPerm.StateVar
