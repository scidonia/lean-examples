/-
Compile-time checks for `Scidonia.FracPerm.StateVar.SealedStateVar`.

`SealedStateVar` is the interface a state variable joins when its type *is* a
layout's state type, up to one equality: it supplies the layout and the equality
and nothing else. The checks are of four kinds:

* **Reads and writes** through the class on the two instances the library ships
  (`Array (UInt64 × UInt64)` and `Array (Array UInt64)`): a leaf read, an
  out-of-bounds read, and the writes' values and reports.
* **The theorems**, spelled out at the concrete instances: detachment, the
  read-after-write, the snapshot, the frame on a disjoint path and the failure
  equation.
* **The absence of the fields**: an instance cannot give the class an `observe`
  or an `encodeRead`, and `rep` cannot name a layout the type is not. The pinned
  messages are what elaboration reports; each is beside an affirmative `#check`
  of a public name in the same file.
* **The comparison with the old class**: `LawfulStateVar` admits an instance
  whose read returns the mutable array — the countermodel of
  `ScidoniaTest/Model5.lean` — and `SealedStateVar` has no field to put that read
  in.

The last section prints the axioms of representative theorems, so that an
inherited kernel principle can be told from a new assumption.
-/
import ScidoniaTest.Model5

open Scidonia.FracPerm.StateVar
open Scidonia.FracPerm.StateVar.Layout5

namespace ScidoniaTest.Sealed

/-! ## The states and paths the checks use -/

/-- The array the sealed checks run on: eight structs, each a machine word paired
with a different one. -/
def demo : Array (UInt64 × UInt64) :=
  #[(0, 100), (1, 101), (2, 102), (7, 103), (4, 104), (5, 105), (6, 106), (7, 107)]

/-- The first field of the struct at index 3, at the sealed array-of-structs
layout. -/
def leftPath : Layout5.ObsPath SealedStateVar.sealedPairs :=
  ⟨.index 3 (.left .here), .uint, rfl⟩

/-- The second field of the struct at index 5. -/
def rightPath : Layout5.ObsPath SealedStateVar.sealedPairs :=
  ⟨.index 5 (.right .here), .uint, rfl⟩

/-- The second field of the struct at index 3: the sibling of `leftPath`'s
field. -/
def siblingPath : Layout5.ObsPath SealedStateVar.sealedPairs :=
  ⟨.index 3 (.right .here), .uint, rfl⟩

/-- A path past the end of the array. -/
def badPath : Layout5.ObsPath SealedStateVar.sealedPairs :=
  ⟨.index 9 (.left .here), .uint, rfl⟩

/-- The nested state: three inner arrays of three machine words. -/
def nestedDemo : Array (Array UInt64) := #[#[1, 2, 3], #[4, 5, 6], #[7, 8, 9]]

/-- The second slot of the inner array at index 2, at the sealed nested layout. -/
def nestedPath : Layout5.ObsPath SealedStateVar.sealedNested :=
  ⟨.index 2 (.index 1 .here), .uint, rfl⟩

/-! ## Reads and writes through the class

The library's `read?` and `setLeaf`, at the two shipped instances, with no
per-instance code on the path. -/

/- The leaf reads, the nested leaf, an out-of-bounds index, and the write values:
the selected slot changes, every other slot does not. -/
#guard decide (SealedStateVar.read? leftPath demo = some (.uint 7))
#guard decide (SealedStateVar.read? rightPath demo = some (.uint 105))
#guard decide (SealedStateVar.read? badPath demo = none)
#guard decide (SealedStateVar.read? nestedPath nestedDemo = some (.uint 8))
#guard (SealedStateVar.setLeaf leftPath (9 : UInt64) demo).2
#guard decide ((SealedStateVar.setLeaf leftPath (9 : UInt64) demo).1[3]! = (9, 103))
#guard decide ((SealedStateVar.setLeaf leftPath (9 : UInt64) demo).1[0]! = (0, 100))
#guard decide ((SealedStateVar.setLeaf leftPath (9 : UInt64) demo).1[7]! = (7, 107))
#guard decide ((SealedStateVar.setLeaf leftPath (9 : UInt64) demo).1.size = 8)
#guard (SealedStateVar.setLeaf nestedPath (99 : UInt64) nestedDemo).2
#guard decide ((SealedStateVar.setLeaf nestedPath (99 : UInt64) nestedDemo).1[2]![1]! = 99)
#guard decide ((SealedStateVar.setLeaf nestedPath (99 : UInt64) nestedDemo).1[1]! = #[4, 5, 6])

/-- A sealed write past the end reports `false` and leaves the state alone. -/
example : SealedStateVar.setLeaf badPath (1 : UInt64) demo = (demo, false) :=
  have h : (SealedStateVar.setLeaf badPath (1 : UInt64) demo).2 = false := rfl
  Prod.ext (SealedStateVar.sealedSetLeaf_failed badPath (1 : UInt64) demo h) h

/-! ## The theorems at a concrete instance

Each is the library theorem applied at `Array (UInt64 × UInt64)`, with the two
operands of the snapshot bound to their own states. -/

/-- Every sealed read result is detached from every root. -/
example (h : SealedStateVar.read? leftPath demo = some (.uint 7)) :
    NoRef 0 (Value.uint 7) :=
  SealedStateVar.sealedRead_detached leftPath demo (.uint 7) h 0

/-- Reading the path after a successful write returns the written observation. -/
example (demo' : Array (UInt64 × UInt64))
    (hwrite : SealedStateVar.setLeaf leftPath (9 : UInt64) demo = (demo', true)) :
    SealedStateVar.read? leftPath demo' = some (.uint 9) := by
  have h2 : (SealedStateVar.setLeaf leftPath (9 : UInt64) demo).2 = true :=
    congrArg Prod.snd hwrite
  have h := SealedStateVar.sealedRead_after_setLeaf leftPath (9 : UInt64) demo h2
  rw [show (SealedStateVar.setLeaf leftPath (9 : UInt64) demo).1 = demo' from
    congrArg Prod.fst hwrite] at h
  exact h

/-- The snapshot at `7 → 9`: the value read before the write is 7, from the old
state, and the read after the write is the written 9. -/
example (demo' : Array (UInt64 × UInt64))
    (hread : SealedStateVar.read? leftPath demo = some (.uint 7))
    (hwrite : SealedStateVar.setLeaf leftPath (9 : UInt64) demo = (demo', true)) :
    SealedStateVar.read? leftPath demo = some (.uint 7) ∧
      SealedStateVar.read? leftPath demo' = some (.uint 9) :=
  SealedStateVar.sealedSnapshot leftPath demo demo' (.uint 7) (9 : UInt64) hread hwrite

/-- The sibling field of the same struct is a disjoint read path: the write does
not change what it reads. -/
example (demo' : Array (UInt64 × UInt64))
    (hwrite : SealedStateVar.setLeaf leftPath (9 : UInt64) demo = (demo', true)) :
    SealedStateVar.read? siblingPath demo' = SealedStateVar.read? siblingPath demo :=
  SealedStateVar.sealedRead_frame leftPath siblingPath demo demo' (9 : UInt64)
    ((Layout5.disjoint_index_iff 3).mpr (Layout5.disjoint_left_right _ _)) hwrite

/-! ## The fields an instance cannot supply

`SealedStateVar` declares the layout and the equality, and nothing else. An
instance that tries to add a read or an encoding is rejected by elaboration, and
so is an equality that names a layout the type is not. The pinned messages are
what elaboration reports. -/

/- The affirmative control for the pins below: the class's own fields resolve. -/
#check @SealedStateVar.layout
#check @SealedStateVar.rep

/- The library's read and write resolve for a sealed type. -/
#check SealedStateVar.read?
#check SealedStateVar.setLeaf

/--
error: `observe` is not a field of structure `SealedStateVar`
-/
#guard_msgs in
instance : SealedStateVar (Array (UInt64 × UInt64)) where
  layout := SealedStateVar.sealedPairs
  rep := rfl
  observe := fun _ s => s

/--
error: `encodeRead` is not a field of structure `SealedStateVar`
-/
#guard_msgs in
instance : SealedStateVar (Array (UInt64 × UInt64)) where
  layout := SealedStateVar.sealedPairs
  rep := rfl
  encodeRead := fun _ _ => .unit

/--
error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  Array UInt64 = State ((Layout.leaf ObsDesc.uint).struct (Layout.leaf ObsDesc.uint)).arr
-/
#guard_msgs in
instance : SealedStateVar (Array UInt64) where
  layout := .arr (.struct (.leaf .uint) (.leaf .uint))
  rep := rfl

/- The class declares no `observe`: a client cannot even name one. -/
/--
error: Unknown constant `Scidonia.FracPerm.StateVar.SealedStateVar.observe`
-/
#guard_msgs in
#check SealedStateVar.observe

/- Nor an `encodeRead`. -/
/--
error: Unknown constant `Scidonia.FracPerm.StateVar.SealedStateVar.encodeRead`
-/
#guard_msgs in
#check SealedStateVar.encodeRead

/-! ## The comparison with the old class

The old class asks the author for a read and an encoding, so it accepts an
instance whose read returns the mutable array: `ScidoniaTest/Model5.lean`'s
countermodel satisfies all four laws. The sealed class has no field to put that
read in — the same instance shape is rejected above — which is what makes its
guarantee structural rather than per-instance. -/

/-- The old class admits the leaky read: `LawfulStateVar.observe` is a field, and
the countermodel's read *is* the state. -/
example (a : Array UInt64) :
    LawfulStateVar.observe (self := ScidoniaTest.Model5.leakyArrayStateVar) () a = a :=
  ScidoniaTest.Model5.leakyArray_read_returns_state a

/- And here is the same instance shape offered to the sealed class: rejected,
because the class has no `observe` field for it. -/
/--
error: `observe` is not a field of structure `SealedStateVar`
-/
#guard_msgs in
instance : SealedStateVar (Array UInt64) where
  layout := .arr (.leaf .uint)
  rep := rfl
  observe := fun _ s => s

/-- The affirmative control: the *layout* named above is a real sealed instance
without the read — the rejection is the missing field, not the type. -/
example : SealedStateVar (Array UInt64) := ⟨.arr (.leaf .uint), rfl⟩

/-! ## Axioms of representative theorems

Only the standard kernel principles — `propext`, `Classical.choice`,
`Quot.sound` — may appear; a name of this development appearing here would be a
new assumption. -/

#print axioms SealedStateVar.sealedLawful_Result
#print axioms SealedStateVar.sealedLawful_encodeRead
#print axioms SealedStateVar.sealedRead_detached
#print axioms SealedStateVar.sealedRead_after_setLeaf
#print axioms SealedStateVar.sealedSnapshot
#print axioms SealedStateVar.sealedRead_frame
#print axioms SealedStateVar.sealedSetLeaf_failed
#print axioms SealedStateVar.toState_ofState

end ScidoniaTest.Sealed
