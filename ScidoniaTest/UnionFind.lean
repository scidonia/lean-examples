/-
Checks for `ScidoniaExamples.UnionFind` from outside the module, so they see what
a client of the example sees.

The instrument differs per kind of check:

* **The algorithm, evaluated.** The arrays are `Array UInt64` and every write is
  `SealedStateVar.setLeaf`, whose traversal reads the array, so the kernel cannot
  reduce a run: the partitions below are `#guard`s, which evaluate the compiled
  definitions. They assert the representative `find` reports for each of eight
  elements after the four unions of `smallSchedule`, that the two runs of those
  unions — the disciplined one and the aliased one — leave the same partition and
  the same parent array, and that `find` on the untouched singletons is the
  identity. Two of the guards have a control of the same shape whose message is
  pinned, so a guard is shown to fire rather than to pass whatever it is given.
* **The discipline, at the algorithm's write path.** The write `find`'s path
  halving and `union`'s link make is the sealed class's write at `wordPath i`, so
  the class's laws hold of it: the read-back at the written slot is the word
  written, and a write at one slot leaves another slot's read alone. Both are
  stated at `setLeaf` with the write's equation a hypothesis, which is what the
  evaluation above establishes and what the kernel cannot reduce.
* **Axioms.** The two theorems print the principles they rest on.
-/
import ScidoniaExamples.UnionFind

open Scidonia.FracPerm.StateVar
open ScidoniaExamples.UnionFind

namespace ScidoniaTest.UnionFind

/-! ## The algorithm, evaluated

The run the guards evaluate: eight singletons, the four unions of
`smallSchedule`, and the partition `find` reports from the array those unions
left. -/

/-- The parent array the checks run on: eight singletons, each its own root. -/
def demoParent : Array UInt64 := singletons smallElements

/-- The rank array the checks run on: eight zeros, every element a tree of depth
zero. -/
def demoRanks : Array UInt64 := zeroRanks smallElements

/-- The parent array the four unions of `smallSchedule` leave, run with the two
arrays the caller alone refers to. -/
def demoUnionParent : Array UInt64 :=
  (runDisciplined smallElements smallSchedule demoParent demoRanks).1

/-- The partition those four unions leave, as `find` reports it from the array
they left: `0` to `3` in one set, `4` and `5` in another, `6` and `7` each
alone. -/
def demoRoots : Array Nat := (representatives smallElements demoUnionParent).2

/- `find` on an untouched array is the identity: every element's parent is
itself, so no path is halved and the representative is the element. -/
#guard decide ((find smallElements demoParent 3).2 = 3)
#guard decide ((find smallElements demoParent 7).2 = 7)

/- One union, evaluated: `1` is linked under `0`, and both elements' root is
`0` whichever of the two a find starts from. -/
#guard decide ((find smallElements (union smallElements demoParent demoRanks 0 1).1 1).2 = 0)
#guard decide ((find smallElements (union smallElements demoParent demoRanks 0 1).1 0).2 = 0)

/- The partition the four unions leave, and the size of the array it is read
from: the answer is not a truncation. -/
#guard decide (demoRoots = #[0, 0, 0, 0, 4, 4, 6, 7])
#guard decide (demoRoots.size = smallElements)

/- Every representative the partition reports is its own parent, read from the
array the unions left: the reported roots are roots. -/
#guard decide (demoRoots.map (fun r => parentOf demoUnionParent r) = demoRoots)

/- The two runs of the same unions leave the same arrays and the same partition.
The aliased shape costs a copy per step and changes nothing about the answer. -/
#guard decide ((runAliased smallElements smallSchedule demoParent demoRanks).1 = demoUnionParent)
#guard decide ((runAliased smallElements smallSchedule demoParent demoRanks).2.1
  = (runDisciplined smallElements smallSchedule demoParent demoRanks).2)
#guard decide ((representatives smallElements
  (runAliased smallElements smallSchedule demoParent demoRanks).1).2 = demoRoots)

/--
error: Expression
  decide (demoRoots = #[0, 0, 0, 0, 4, 4, 6, 8])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (demoRoots = #[0, 0, 0, 0, 4, 4, 6, 8])

/--
error: Expression
  decide ((find smallElements demoParent 3).snd = 4)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((find smallElements demoParent 3).2 = 4)

/-! ## The discipline, at the algorithm's write path

`find`'s path-halving write and `union`'s link are both the same write: the
sealed class's `setLeaf` at `wordPath i`. So the class's laws are the algorithm's,
and the two below are the two the algorithm leans on — that a write at a slot is
read back at that slot, and that it leaves every other slot's read alone. -/

/-- The write the union-find performs, read back: a sealed write at `wordPath i`
that reported success reads, at that path, as the word it was handed. -/
theorem setLeaf_read_after (a a' : Array UInt64) (i : Nat) (v : UInt64)
    (h : SealedStateVar.setLeaf (σ := Array UInt64) (wordPath i) v a = (a', true)) :
    SealedStateVar.read? (wordPath i) a' = some (.uint v) := by
  have hw : (SealedStateVar.setLeaf (σ := Array UInt64) (wordPath i) v a).2 = true :=
    congrArg Prod.snd h
  have hread := SealedStateVar.sealedRead_after_setLeaf (wordPath i) v a hw
  rw [show (SealedStateVar.setLeaf (σ := Array UInt64) (wordPath i) v a).1 = a' from
    congrArg Prod.fst h] at hread
  rwa [show Layout5.encodeObs (wordPath i).obs v = (Value.uint v) from rfl] at hread

/-- The write does not change what another slot reads: `find`'s path-halving
write and `union`'s link are writes at one slot of the flat array, and two
different slots are disjoint paths. -/
theorem setLeaf_read_frame (a a' : Array UInt64) (i j : Nat) (v : UInt64) (hij : i ≠ j)
    (h : SealedStateVar.setLeaf (σ := Array UInt64) (wordPath i) v a = (a', true)) :
    SealedStateVar.read? (wordPath j) a' = SealedStateVar.read? (wordPath j) a :=
  SealedStateVar.sealedRead_frame (p := wordPath i) (q := wordPath j) a a' v
    (Layout5.disjoint_index_ne hij) h

/-! ## The axioms of the theorems stated here

Only the standard kernel principles — `propext`, `Classical.choice`,
`Quot.sound` — may appear; a name of this development appearing here would be a
new assumption. -/

#print axioms setLeaf_read_after
#print axioms setLeaf_read_frame

end ScidoniaTest.UnionFind
