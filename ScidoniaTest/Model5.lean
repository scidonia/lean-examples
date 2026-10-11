/-
Compile-time checks for Model 5, `Scidonia.FracPerm.StateVar.Layout5`.

These live in the check library, so they see exactly what a client sees. The
checks are of four kinds:

* **Reads** are behavioural: `read?` at a leaf of an array of structs, at a
  nested struct, and at an out-of-bounds index, with the whole-array read
  rejected by elaboration. The observation universe is closed, so a read result
  is immutable data of `ObsEl o`.
* **The zipper's** laws are theorems spelled out at concrete paths: opening and
  plugging, the path replacement, and the failure equation, at a non-last index,
  the last index and an out-of-bounds index.
* **Frames and snapshots** bind the two operands to their own states: an earlier
  read's value comes from the old state while the read after the write encodes
  the write's operand, and a disjoint read is unchanged. A same-path control
  shows the value really changed.
* **The old class** is compared against: a countermodel instance whose read
  returns the mutable array itself satisfies all four class laws, because the
  class constrains the author's encoding rather than the state it names. Model 5
  cannot be entered that way: its read has no array to return and its path
  cannot address one.

The last section prints the axioms of representative theorems, so that an
inherited kernel principle can be told from a new assumption.
-/
import Scidonia.FracPerm

open Scidonia.FracPerm.StateVar
open Scidonia.FracPerm.StateVar.Layout5

namespace ScidoniaTest.Model5

/-! ## The layouts and paths the checks use

An array of binary structs of machine words, a nested struct with a natural and
a boolean leaf, and the paths into them. -/

/-- An array of binary structs, each a pair of machine words: the layout the
take-out write's checks use. -/
abbrev pairs : Layout5.Layout := .arr (.struct (.leaf .uint) (.leaf .uint))

/-- A struct of a struct of a word and a natural, and a boolean: a leaf need not
be a machine word, and a struct may nest. -/
abbrev nested : Layout5.Layout :=
  .struct (.struct (.leaf .uint) (.leaf .nat)) (.leaf .bool)

/-- The first field of the struct at index 3: neither the first nor the last
slot. -/
def leftPath : Layout5.ObsPath pairs := ⟨.index 3 (.left .here), .uint, rfl⟩

/-- The second field of the struct at index 5. -/
def rightPath : Layout5.ObsPath pairs := ⟨.index 5 (.right .here), .uint, rfl⟩

/-- The second field of the struct at index 3: the sibling of `leftPath`'s
field. -/
def siblingPath : Layout5.ObsPath pairs := ⟨.index 3 (.right .here), .uint, rfl⟩

/-- The first field of the last struct. -/
def lastPath : Layout5.ObsPath pairs := ⟨.index 7 (.left .here), .uint, rfl⟩

/-- A path past the end of the array. -/
def badPath : Layout5.ObsPath pairs := ⟨.index 9 (.left .here), .uint, rfl⟩

/-- The right field of the inner struct of the nested layout: the natural
leaf. -/
def nestedPath : Layout5.ObsPath nested := ⟨.left (.right .here), .nat, rfl⟩

/-- A root leaf: the whole layout is one word, so the root path is a leaf
path. -/
def rootPath : Layout5.ObsPath (.leaf .uint) := ⟨.here, .uint, rfl⟩

/-- The array the read and write checks run on: eight structs, each a machine
word paired with a different one. -/
def demo : Layout5.State pairs :=
  #[(0, 100), (1, 101), (2, 102), (7, 103), (4, 104), (5, 105), (6, 106), (7, 107)]

/-- The nested state: the word 4 and the natural 9 inside the left component, and
`true` as the right one. -/
def demoNested : Layout5.State nested := ((4, 9), true)

/-! ## Reads

A leaf read gives the library's encoding of an immutable observation, an
out-of-bounds index gives nothing, and the encoding is injective and detached
for *every* description. -/

/- The leaf reads: the first field of the struct at index 3, the last struct's
first field, the second field of another struct, the nested natural, and a root
leaf. -/
#guard decide (Layout5.read? leftPath demo = some (.uint 7))
#guard decide (Layout5.read? lastPath demo = some (.uint 7))
#guard decide (Layout5.read? rightPath demo = some (.uint 105))
#guard decide (Layout5.read? nestedPath demoNested = some (.nat 9))
#guard decide (Layout5.read? rootPath (7 : UInt64) = some (.uint 7))

/- An out-of-bounds index gives nothing rather than a default. -/
#guard decide (Layout5.read? badPath demo = none)

/-- `encodeObs` distinguishes observations of every description: this is the law
the adapter's encoding inherits, quantified over the whole universe rather than
asserted per description. -/
example (o : ObsDesc) (x y : ObsEl o) (h : Layout5.encodeObs o x = Layout5.encodeObs o y) :
    x = y :=
  Layout5.encodeObs_injective o x y h

/-- An observation of every description is detached from every root. -/
example (ℓ : Loc) (o : ObsDesc) (x : ObsEl o) : NoRef ℓ (Layout5.encodeObs o x) :=
  Layout5.encodeObs_noRef ℓ o x

/-- The detector has a negative control as well: the root's own location is
*not* detached from it, so a passing `NoRef` above is not vacuous. -/
example : ¬ NoRef 0 (Value.loc 0) := not_noRef_loc_self 0

/-- The read at a concrete leaf is detached from the array's own root: the
result is `.uint 7`, an immutable observation. -/
example (h : Layout5.read? leftPath demo = some (.uint 7)) :
    NoRef 0 (Value.uint 7) :=
  Layout5.read_detached leftPath demo (.uint 7) h 0

/- The whole-array read is rejected by the *types*: an `ObsPath` for `.arr`
would need `At .here = .leaf o`, and a here-path at an array ends at the array.
The pinned message is the elaboration error a client sees. -/
/--
error: Application type mismatch: The argument
  rfl
has type
  ?m.4 = ?m.4
but is expected to have type
  Layout5.At Path.here = Layout.leaf ObsDesc.uint
in the application
  { path := Path.here, obs := ObsDesc.uint, leaf := ⋯ }
-/
#guard_msgs in
example : Layout5.ObsPath (.arr (.leaf .uint)) := ⟨.here, .uint, rfl⟩

/-- The same fact as a theorem: a here-path at an array root is not a leaf of
the observation universe, so no `ObsPath` addresses a whole array. -/
example (o : ObsDesc) :
    Layout5.At (Layout5.Path.here : Layout5.Path (.arr (.leaf .uint))) ≠ .leaf o :=
  Layout5.array_root_not_observable o

/-- A root that *is* a leaf reads: the affirmative control beside the rejected
array root. -/
example : (Layout5.ObsPath (.leaf .uint)) := rootPath

/-! ## The public surface

The take-out and the zipper are *private*. The public read is `read?` and the
public write is `setLeaf`, and neither hands back a state: the take-out
(`takeOut`) that hands the extracted element over, the put-back (`plugAt`), the
one-hole context and the zipper operations are all names a client cannot reach.
The generic round-trip and failure laws are internal lemmas, exercised through
the public surface by the reads, the write values and the snapshot below. -/

/- The take-out is not part of the surface: it returns the raw element an update
below a path works on, so a client cannot obtain a mutable object the state
still holds. The pinned message is what elaboration reports. -/
/--
error: Unknown identifier `takeOut`
-/
#guard_msgs in
#check takeOut

/- Nor the put-back that installs an element back in a slot. -/
/--
error: Unknown identifier `plugAt`
-/
#guard_msgs in
#check plugAt

/- A client cannot name `open`: it is the raw-focus route out of a state. The
pinned message is what elaboration reports. -/
/--
error: Unknown identifier `«open»`
-/
#guard_msgs in
#check «open»

/- Nor the zipper's fill operation. -/
/--
error: Unknown identifier `plug`
-/
#guard_msgs in
#check plug

/- Nor the one-hole context type itself: with `plug` private it would be inert,
but it is not part of the surface either. -/
/--
error: Unknown identifier `Context`
-/
#guard_msgs in
#check Context

/- The affirmative control for those pins: a public name of the same namespace
resolves here, so what they observe is the privacy of the other names rather
than an unopened namespace or a misspelled module. -/
#check read?

/- The write's values: it took effect, it changed the selected slot, and every
other slot — the sibling field of the same struct and the neighbouring structs —
is unchanged. -/
#guard (Layout5.setLeaf leftPath (99 : UInt64) demo).2
#guard decide ((Layout5.setLeaf leftPath (99 : UInt64) demo).1[3]! = (99, 103))
#guard decide ((Layout5.setLeaf leftPath (99 : UInt64) demo).1[0]! = (0, 100))
#guard decide ((Layout5.setLeaf leftPath (99 : UInt64) demo).1[2]! = (2, 102))
#guard decide ((Layout5.setLeaf leftPath (99 : UInt64) demo).1[4]! = (4, 104))
#guard decide ((Layout5.setLeaf leftPath (99 : UInt64) demo).1[7]! = (7, 107))
#guard decide ((Layout5.setLeaf leftPath (99 : UInt64) demo).1.size = 8)

/- The last slot, where the take-out's index is the array's last, and the
second field of a struct: the write lands at the path either way. -/
#guard (Layout5.setLeaf lastPath (8 : UInt64) demo).2
#guard decide ((Layout5.setLeaf lastPath (8 : UInt64) demo).1[7]! = (8, 107))
#guard (Layout5.setLeaf rightPath (1050 : UInt64) demo).2
#guard decide ((Layout5.setLeaf rightPath (1050 : UInt64) demo).1[5]! = (5, 1050))

/-- An out-of-bounds write reports `false` and leaves the state alone. -/
example :
    Layout5.setLeaf badPath (1 : UInt64) demo = (demo, false) :=
  have h : (Layout5.setLeaf badPath (1 : UInt64) demo).2 = false := rfl
  Prod.ext (Layout5.setLeaf_failed badPath (1 : UInt64) demo h) h

/-! ## Frames and snapshots

The two observations are bound to their own states: the earlier read's value
comes from the state before the write, and the read after the write encodes the
write's operand. The same path is read before and after, and the two values
differ — so the first conjunct cannot satisfy the criterion by reflexivity. -/

/- The concrete `7` → `9` readings, evaluated: the state reads 7 at the path,
and the state the write produces reads 9. The `#guard`s are what establish the
two concrete values; the kernel cannot reduce `read?` on an `Array` literal,
because `Array`'s primitives are opaque to it, so the theorems below take the
first reading as an assumption rather than proving it by `rfl`. -/
#guard decide (Layout5.read? leftPath demo = some (.uint 7))
#guard decide (Layout5.read? leftPath (Layout5.setLeaf leftPath (9 : UInt64) demo).1 = some (.uint 9))

/-- The snapshot at `7 → 9`: the value read before the write is 7, from the old
state, and the read after the write is the written 9. The two operands are the
two different readings, not two occurrences of one value. -/
example (demo' : Layout5.State pairs)
    (hread : Layout5.read? leftPath demo = some (.uint 7))
    (hwrite : Layout5.setLeaf leftPath (9 : UInt64) demo = (demo', true)) :
    Layout5.read? leftPath demo = some (.uint 7) ∧
      Layout5.read? leftPath demo' = some (.uint 9) :=
  Layout5.snapshot_after_setLeaf leftPath demo demo' (.uint 7) (9 : UInt64) hread hwrite

/-- The sibling field of the same struct is a disjoint read path: writing the
left field does not change what the right field reads. -/
example (demo' : Layout5.State pairs)
    (hwrite : Layout5.setLeaf leftPath (9 : UInt64) demo = (demo', true)) :
    Layout5.read? siblingPath demo' = Layout5.read? siblingPath demo :=
  Layout5.read_frame leftPath siblingPath demo demo' (9 : UInt64)
    ((Layout5.disjoint_index_iff 3).mpr (Layout5.disjoint_left_right _ _)) hwrite

/-- Another array index is disjoint from the written one, even though both paths
address the same field of their structs. -/
example (demo' : Layout5.State pairs)
    (hwrite : Layout5.setLeaf leftPath (9 : UInt64) demo = (demo', true)) :
    Layout5.read? rightPath demo' = Layout5.read? rightPath demo :=
  Layout5.read_frame leftPath rightPath demo demo' (9 : UInt64)
    ((Layout5.disjoint_index_ne (i := 3) (j := 5)
      (p := Layout5.Path.left Layout5.Path.here)
      (q := Layout5.Path.right Layout5.Path.here) (by decide))) hwrite

/-- The same-path control: the write changes what the written path reads, which
is why the frame law needs `Disjoint` and not merely "a different path". -/
example (demo' : Layout5.State pairs)
    (hread : Layout5.read? leftPath demo = some (.uint 7))
    (hread' : Layout5.read? leftPath demo' = some (.uint 9)) :
    Layout5.read? leftPath demo ≠ Layout5.read? leftPath demo' := by
  rw [hread, hread']
  decide

/-! ## The old class admits the counterexample

The old class's obligations are about the author's chosen encoding, not about
the state a read names. Here is an instance that satisfies all four laws and
whose read hands back the mutable array itself: its encoding is a
constructor-faithful nesting of pairs, so it is injective and names no `.loc`,
while the value it encodes is the whole array. -/

/-- A constructor-faithful encoding of a list of words as nested pairs. -/
def encodeList : List UInt64 → Value
  | [] => .unit
  | x :: xs => .pair (.uint x) (encodeList xs)

/-- `encodeList` is injective: the encoding distinguishes lists. -/
theorem encodeList_injective : ∀ l₁ l₂ : List UInt64, encodeList l₁ = encodeList l₂ → l₁ = l₂
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => absurd h (by simp [encodeList])
  | _ :: _, [] => fun h => absurd h (by simp [encodeList])
  | x :: xs, y :: ys => fun h => by
      have h1 : Value.uint x = Value.uint y := (Value.pair.inj h).1
      have h2 : encodeList xs = encodeList ys := (Value.pair.inj h).2
      rw [Value.uint.inj h1, encodeList_injective xs ys h2]

/-- The same encoding names no `.loc`: it is built from `.uint` and `.pair`
alone. -/
theorem encodeList_noRef (ℓ : Loc) : ∀ l : List UInt64, NoRef ℓ (encodeList l)
  | [] => trivial
  | _ :: xs => ⟨trivial, encodeList_noRef ℓ xs⟩

/-- The encoding of a whole array: a nesting of pairs of its elements. -/
def encodeArray (a : Array UInt64) : Value := encodeList a.toList

/-- The array encoding is injective, so the counterexample can prove the class's
encoding law rather than assert it. -/
theorem encodeArray_injective (a b : Array UInt64) (h : encodeArray a = encodeArray b) : a = b :=
  Array.toList_inj.mp (encodeList_injective a.toList b.toList h)

/-- The array encoding names no `.loc`, so the class's no-reference law holds of
it. -/
theorem encodeArray_noRef (ℓ : Loc) (a : Array UInt64) : NoRef ℓ (encodeArray a) :=
  encodeList_noRef ℓ a.toList

/-- The counterexample: a state variable whose read returns the state itself.
Every class law holds — the encoding is constructor-faithful — so the class
accepts it, and a client's read is handed the mutable array. -/
@[instance_reducible] def leakyArrayStateVar : LawfulStateVar (Array UInt64) Unit Unit Unit where
  Result _ := Array UInt64
  initial _ := #[]
  Valid _ := True
  observe _ s := s
  replace _ s := (s, true)
  encodeRead _ a := encodeArray a
  initial_valid _ := trivial
  replace_valid _ _ _ := trivial
  encodeRead_injective _ a b h := encodeArray_injective a b h
  observe_detached ℓ _ a _ := encodeArray_noRef ℓ a

/-- The counterexample's read is the state itself: a client holding this result
holds the array. -/
theorem leakyArray_read_returns_state (a : Array UInt64) :
    LawfulStateVar.observe (self := leakyArrayStateVar) () a = a := rfl

/-- And its encoding presents the whole mutable array as immutable nested data —
`.pair (.uint 7) (.pair (.uint 8) .unit)` for `#[7, 8]` — which is exactly the
gap the class's laws do not close. -/
theorem leakyArray_encoding_of_two :
    LawfulStateVar.encodeRead (self := leakyArrayStateVar) ()
      (LawfulStateVar.observe (self := leakyArrayStateVar) () (#[7, 8] : Array UInt64)) =
      Value.pair (Value.uint 7) (Value.pair (Value.uint 8) Value.unit) := rfl

/- Model 5's read of the same kind of state cannot return the array: its result
is an encoded observation of the closed universe, and the read of a leaf is an
`Option Value`. -/
#guard (Layout5.read? leftPath demo).isSome

/-- The class's own detector still answers for the countermodel: a location at
the root it names is not detached. -/
theorem leaky_root_not_detached : ¬ NoRef 0 (Value.loc 0) := not_noRef_loc_self 0

/-! ## The adapter's laws at the layout state

The adapter is the library's own: its observations are `read?`'s, its writes are
`setLeaf`'s, and its encoding is `encodeObs`. The generic model's theorems and
the heap's apply at it without a new proof. -/

/-- Reading back after a successful adapter write returns the written
observation. -/
example (s : Layout5.DescribedLayout pairs)
    (h : (Layout5.setLeaf leftPath (9 : UInt64) s.value).2 = true) :
    (Layout5.describedLayoutStateVar pairs).observe leftPath
      ((Layout5.describedLayoutStateVar pairs).replace ⟨leftPath, (9 : UInt64)⟩ s).1 =
      some (9 : UInt64) :=
  Layout5.describedLayout_read_after_replace pairs leftPath (9 : UInt64) s h

/-- A failed adapter write leaves the wrapped state alone. -/
example (s : Layout5.DescribedLayout pairs)
    (h : (Layout5.setLeaf badPath (1 : UInt64) s.value).2 = false) :
    ((Layout5.describedLayoutStateVar pairs).replace ⟨badPath, (1 : UInt64)⟩ s).1 = s :=
  Layout5.describedLayout_replace_failed pairs badPath (1 : UInt64) s h

/-- The adapter's observations are detached from every root: the class's
no-reference law at the adapter's own encoding. -/
example (ℓ : Loc) (s : Layout5.DescribedLayout pairs) :
    NoRef ℓ ((Layout5.describedLayoutStateVar pairs).encodeRead leftPath
      ((Layout5.describedLayoutStateVar pairs).observe leftPath s)) :=
  Layout5.describedLayout_primitive_detached pairs ℓ leftPath s

/-- The adapter's encoding of a read result is `encodeObs` of the observation:
no instance author supplies it. -/
example (x : Layout5.ObsEl leftPath.obs) :
    (Layout5.describedLayoutStateVar pairs).encodeRead leftPath (some x) =
      .some (Layout5.encodeObs leftPath.obs x) := rfl

/-- The heap's read transition at the adapter: what a read of a root holding a
layout state returns is detached from that root. -/
example {ℓ : Loc} {h h' : Heap (Layout5.DescribedLayout pairs)}
    {v : Option (Layout5.ObsEl leftPath.obs)}
    (hr : ReadAt (Layout5.describedLayoutStateVar pairs) ℓ leftPath h h' v) :
    NoRef ℓ ((Layout5.describedLayoutStateVar pairs).encodeRead leftPath v) :=
  Layout5.describedLayout_read_at_detached pairs hr

/-- The heap's write transition at the adapter: a write leaves an admissible
state in the root cell. -/
example {ℓ : Loc} {w : Layout5.LayoutWrite pairs}
    {h h' : Heap (Layout5.DescribedLayout pairs)} {b : Bool}
    (hw : WriteAt (Layout5.describedLayoutStateVar pairs) ℓ w h h' b) :
    ∃ s', Scidonia.FracPerm.StateVar.At ℓ s' h' ∧
      (Layout5.describedLayoutStateVar pairs).Valid s' :=
  Layout5.describedLayout_write_at_valid pairs hw

/-- The heap's frame at the adapter: a write changes no other cell. -/
example {ℓ m : Loc} {w : Layout5.LayoutWrite pairs}
    {h h' : Heap (Layout5.DescribedLayout pairs)} {b : Bool}
    (hw : WriteAt (Layout5.describedLayoutStateVar pairs) ℓ w h h' b) (hm : m ≠ ℓ) :
    h' m = h m :=
  Layout5.describedLayout_write_at_frame pairs hw hm

/-! ## Axioms of representative theorems

Only the standard kernel principles — `propext`, `Classical.choice`,
`Quot.sound` — may appear; a name of this development appearing here would be a
new assumption. -/

#print axioms Scidonia.FracPerm.StateVar.Layout5.encodeObs_injective
#print axioms Scidonia.FracPerm.StateVar.Layout5.encodeObs_noRef
#print axioms Scidonia.FracPerm.StateVar.Layout5.read_detached
#print axioms Scidonia.FracPerm.StateVar.Layout5.setLeaf_failed
#print axioms Scidonia.FracPerm.StateVar.Layout5.snapshot_after_setLeaf
#print axioms Scidonia.FracPerm.StateVar.Layout5.read?_leafAt?
#print axioms Scidonia.FracPerm.StateVar.Layout5.read_frame
#print axioms Scidonia.FracPerm.StateVar.Layout5.describedLayout_read_after_replace
#print axioms Scidonia.FracPerm.StateVar.Layout5.describedLayout_primitive_detached
#print axioms Scidonia.FracPerm.StateVar.Layout5.array_root_not_observable

end ScidoniaTest.Model5
