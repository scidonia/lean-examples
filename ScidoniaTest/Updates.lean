/-
Checks for `ScidoniaExamples.Updates` from outside the module, so they see what
a client of the examples sees.

The checks are of three kinds, and the instrument differs per example — which is
the point of the example set:

* **The flat array.** `arrSet` is `Array.set!`, and the kernel cannot reduce
  `Array`'s primitives on a literal, so the concrete values are `#guard`s, which
  evaluate the compiled definitions. The two theorems are the general ones the
  primitive supports — the written index and every other index — and they are
  proved from the primitive's own lemmas.
* **The nested array.** The write is `SealedStateVar.setLeaf` at a two-step path,
  whose traversal reads the outer array, so the write's report is not something
  the kernel reduces either: the concrete readings are `#guard`s, and the
  theorems apply the sealed discipline's own theorems with the write's equation a
  hypothesis — `sealedRead_after_setLeaf`, `sealedSnapshot`, `sealedRead_frame` at
  a sibling slot and at another inner array.
* **The struct tree.** The tree is pairs all the way down, so the kernel reduces
  its writes, its reads and its paths: every check below is a closed theorem and
  the write's equation is proved by `rfl` rather than assumed.

The last section prints the axioms of the theorems stated here.
-/
import ScidoniaExamples.Updates

open Scidonia.FracPerm.StateVar
open Scidonia.FracPerm.StateVar.Layout5
open ScidoniaExamples.Updates

namespace ScidoniaTest.Updates

/-! ## The flat array

The update lands at the index it names and leaves every other index alone; the
demo's values are evaluated, and the theorems are the primitive's own two facts
at the example's function. -/

/-- The flat array the checks run on: four machine words. -/
def flatDemo : Array UInt64 := #[10, 11, 12, 13]

/-- The update lands at the index it names: the slot holds the written word. -/
theorem arrSet_getElem?_self {a : Array UInt64} {i : Nat} (h : i < a.size) (v : UInt64) :
    (arrSet a i v)[i]? = some v := by
  simp [arrSet, Array.getElem?_setIfInBounds_self_of_lt h]

/-- The update leaves every other index alone: the frame at a sibling index. -/
theorem arrSet_getElem?_ne {a : Array UInt64} {i j : Nat} (h : i ≠ j) (v : UInt64) :
    (arrSet a i v)[j]? = a[j]? := by
  simp [arrSet, Array.getElem?_setIfInBounds_ne h]

/- The demo's values, evaluated: the written slot holds the new word, the three
other slots hold theirs, and the size is unchanged. There is no guard for an
out-of-bounds index: compiled, `Array.set!` is `lean_array_set`, which panics on
one, so such a guard would never reach its assertion. -/
#guard decide ((arrSet flatDemo 1 99)[1]? = some 99)
#guard decide ((arrSet flatDemo 1 99)[0]? = some 10)
#guard decide ((arrSet flatDemo 1 99)[2]? = some 12)
#guard decide ((arrSet flatDemo 1 99)[3]? = some 13)
#guard decide ((arrSet flatDemo 1 99).size = flatDemo.size)

/-! ## The nested array

The write's report and the readings around it are evaluated — the path's
`inBounds` reads the outer array, which the kernel does not reduce — and the
sealed theorems are then applied with the write's equation as the hypothesis the
evaluation establishes. Both operands of each statement are bound to the state
they belong to, so the second conjunct of the snapshot cannot stand in for the
first. -/

/-- The nested array the checks run on: three inner arrays of three machine
words. -/
def nestedDemo : Array (Array UInt64) := #[#[1, 2, 3], #[4, 5, 6], #[7, 8, 9]]

/-- The path the nested checks write: slot `1` of the inner array at index `2`,
whose word is `8` before the write. -/
def nestedWritePath : Layout5.ObsPath SealedStateVar.sealedNested := nestedPath 2 1

/-- The sibling slot of the same inner array, which the write does not reach. -/
def nestedSiblingPath : Layout5.ObsPath SealedStateVar.sealedNested := nestedPath 2 0

/-- Another inner array, whose every slot the write does not reach. -/
def nestedOtherPath : Layout5.ObsPath SealedStateVar.sealedNested := nestedPath 0 1

/- The demo's values, evaluated: the write reports that it took effect, the
written slot holds the new word, the sibling slot and another inner array hold
theirs, and the outer array keeps its size. -/
#guard (nestedSet nestedDemo 2 1 99).2
#guard decide ((nestedSet nestedDemo 2 1 99).1[2]![1]! = 99)
#guard decide ((nestedSet nestedDemo 2 1 99).1[2]![0]! = 7)
#guard decide ((nestedSet nestedDemo 2 1 99).1[2]![2]! = 9)
#guard decide ((nestedSet nestedDemo 2 1 99).1[1]! = #[4, 5, 6])
#guard decide ((nestedSet nestedDemo 2 1 99).1.size = 3)

/- The value the path reads before the write, evaluated: the snapshot's first
conjunct, and the hypothesis its statement takes. -/
#guard decide (SealedStateVar.read? nestedWritePath nestedDemo = some (.uint 8))

/-- Reading the path after a successful write returns the written word. -/
theorem nestedDemo_read_after (demo' : Array (Array UInt64))
    (hwrite : nestedSet nestedDemo 2 1 99 = (demo', true)) :
    SealedStateVar.read? nestedWritePath demo' = some (.uint 99) := by
  have hw : SealedStateVar.setLeaf (σ := Array (Array UInt64)) (nestedPath 2 1) (99 : UInt64)
      nestedDemo = (demo', true) := hwrite
  have h := SealedStateVar.sealedRead_after_setLeaf (nestedPath 2 1) (99 : UInt64) nestedDemo
    (congrArg Prod.snd hw)
  have hfst : (SealedStateVar.setLeaf (σ := Array (Array UInt64)) (nestedPath 2 1) (99 : UInt64)
      nestedDemo).1 = demo' := congrArg Prod.fst hw
  rwa [hfst] at h

/-- The snapshot at `8 → 99`: the read taken before the write keeps the value it
read from the old state, while the read of the state the write produced is the
write's own operand. -/
theorem nestedDemo_snapshot (demo' : Array (Array UInt64))
    (hread : SealedStateVar.read? nestedWritePath nestedDemo = some (.uint 8))
    (hwrite : nestedSet nestedDemo 2 1 99 = (demo', true)) :
    SealedStateVar.read? nestedWritePath nestedDemo = some (.uint 8) ∧
      SealedStateVar.read? nestedWritePath demo' = some (.uint 99) := by
  have hw : SealedStateVar.setLeaf (σ := Array (Array UInt64)) (nestedPath 2 1) (99 : UInt64)
      nestedDemo = (demo', true) := hwrite
  exact SealedStateVar.sealedSnapshot (p := nestedPath 2 1) nestedDemo demo' (.uint 8)
    (99 : UInt64) hread hw

/-- The frame at the sibling slot of the same inner array: the write at slot `1`
does not change what slot `0` reads. -/
theorem nestedDemo_frame (demo' : Array (Array UInt64))
    (hwrite : nestedSet nestedDemo 2 1 99 = (demo', true)) :
    SealedStateVar.read? nestedSiblingPath demo' = SealedStateVar.read? nestedSiblingPath nestedDemo := by
  have hw : SealedStateVar.setLeaf (σ := Array (Array UInt64)) (nestedPath 2 1) (99 : UInt64)
      nestedDemo = (demo', true) := hwrite
  exact SealedStateVar.sealedRead_frame (p := nestedPath 2 1) (q := nestedPath 2 0)
    nestedDemo demo' (99 : UInt64)
    ((Layout5.disjoint_index_iff 2).mpr (Layout5.disjoint_index_ne (i := 1) (j := 0) (by decide)))
    hw

/-- The frame at another inner array: the write at index `2` does not change what
the inner array at index `0` reads. -/
theorem nestedDemo_frame_other (demo' : Array (Array UInt64))
    (hwrite : nestedSet nestedDemo 2 1 99 = (demo', true)) :
    SealedStateVar.read? nestedOtherPath demo' = SealedStateVar.read? nestedOtherPath nestedDemo := by
  have hw : SealedStateVar.setLeaf (σ := Array (Array UInt64)) (nestedPath 2 1) (99 : UInt64)
      nestedDemo = (demo', true) := hwrite
  exact SealedStateVar.sealedRead_frame (p := nestedPath 2 1) (q := nestedPath 0 1)
    nestedDemo demo' (99 : UInt64)
    (Layout5.disjoint_index_ne (i := 2) (j := 0) (by decide)) hw

/-! ## The struct tree

The demo trees are built from the four and the eight words they hold, the write
is a closed equation, and the reads, the snapshot and the frame are all theorems
rather than evaluations. -/

/-- The depth-2 tree with the four given leaves. -/
def tree2 (a b c d : UInt64) : Layout5.State (structTree 2) := ((a, b), (c, d))

/-- The depth-3 tree with the eight given leaves. -/
def tree3 (a b c d e f g h : UInt64) : Layout5.State (structTree 3) :=
  (((a, b), (c, d)), ((e, f), (g, h)))

/-- The depth-2 tree the checks run on: leaves `1, 2, 3, 4` from left to right. -/
def treeDemo : Layout5.State (structTree 2) := tree2 1 2 3 4

/-- The tree the write leaves behind: the leftmost leaf holds `9`. -/
def treeAfter : Layout5.State (structTree 2) := tree2 9 2 3 4

/-- The write at the leftmost leaf of the demo tree, in the terms the sealed
theorems use: the library's `setLeaf` at the tree's layout, reporting `true`.
Proved by reduction, because the tree is pairs and no array is involved. -/
theorem treeDemo_write :
    SealedStateVar.setLeaf (σ := Layout5.State (structTree 2)) (treePath 2) (9 : UInt64) treeDemo
      = (treeAfter, true) := rfl

/-- The same equation through the example's own update: the whole tree the write
leaves, which is the state with the leftmost leaf replaced and every other leaf
fixed. -/
theorem treeSet_treeDemo : treeSet 2 9 treeDemo = (treeAfter, true) := rfl

/-- Reading the path after the write returns the written word. -/
theorem treeDemo_read_after :
    SealedStateVar.read? (treePath 2) (treeSet 2 9 treeDemo).1 = some (.uint 9) :=
  SealedStateVar.sealedRead_after_setLeaf (treePath 2) (9 : UInt64) treeDemo
    (congrArg Prod.snd treeDemo_write)

/-- The snapshot at `1 → 9`: the read of the old tree is the old leaf and the read
of the tree the write left is the written one. -/
theorem treeDemo_snapshot :
    SealedStateVar.read? (treePath 2) treeDemo = some (.uint 1) ∧
      SealedStateVar.read? (treePath 2) treeAfter = some (.uint 9) :=
  SealedStateVar.sealedSnapshot (treePath 2) treeDemo treeAfter (.uint 1) (9 : UInt64)
    rfl treeDemo_write

/-- The frame at the sibling leaf, inside the deepest struct on the written path:
the write at `treePath 2` does not change what `treeSiblingPath 1` reads. -/
theorem treeDemo_frame :
    SealedStateVar.read? (treeSiblingPath 1) treeAfter =
      SealedStateVar.read? (treeSiblingPath 1) treeDemo :=
  SealedStateVar.sealedRead_frame (σ := Layout5.State (structTree 2)) (p := treePath 2)
    (q := treeSiblingPath 1) treeDemo treeAfter (9 : UInt64)
    (treePath_disjoint_sibling 1) treeDemo_write

/-- The sibling leaf's own value, so that the frame above has both sides read:
the leaf beside the written one holds `2` before the write and, by the frame
theorem, after it. -/
theorem treeSibling_value :
    SealedStateVar.read? (treeSiblingPath 1) treeDemo = some (.uint 2) := rfl

/-- The library's builder numbering at depth three, checked against the eight
leaves it names, from the left: the leftmost leaf of `treeFilled 3 10` is `10`
and the tree is the literal one. -/
theorem treeFilled_three : treeFilled 3 10 = tree3 10 11 12 13 14 15 16 17 := rfl

/-- A write one level deeper, through the library's builder: the leftmost leaf
becomes `99` and every other leaf is the one the builder put there. -/
theorem treeFilled_write :
    treeSet 3 99 (treeFilled 3 10) = (tree3 99 11 12 13 14 15 16 17, true) := rfl

/-! ## The axioms of the theorems stated here

Only the standard kernel principles — `propext`, `Classical.choice`,
`Quot.sound` — may appear; a name of this development appearing here would be a
new assumption. -/

#print axioms arrSet_getElem?_self
#print axioms arrSet_getElem?_ne
#print axioms treePath_disjoint_sibling
#print axioms treeSteps_leaf
#print axioms treeSiblingSteps_leaf
#print axioms treeDemo_write
#print axioms treeSet_treeDemo
#print axioms treeDemo_read_after
#print axioms treeDemo_snapshot
#print axioms treeDemo_frame
#print axioms treeSibling_value
#print axioms treeFilled_three
#print axioms treeFilled_write
#print axioms nestedDemo_read_after
#print axioms nestedDemo_snapshot
#print axioms nestedDemo_frame
#print axioms nestedDemo_frame_other

end ScidoniaTest.Updates
