/-
An example library of updates over arrays and trees, written with the
repository's ownership discipline where the discipline applies and with the Lean
primitive where the primitive is the honest vehicle.

Three updates, and the vehicle each one uses:

* `arrSet` on a flat `Array UInt64` is `Array.set!`, the primitive. A flat array
  of machine words *is* the object the interface threads whole: there is no part
  of it a layout describes as a leaf and no path to walk, so the primitive is the
  honest vehicle. The write is one slot — O(1) — when the array is exclusively
  owned, because the compiled `lean_array_set` writes through the buffer the
  caller owns, and it is a whole-buffer copy, O(n), when a second reference to the
  array is live. Which of the two happens is the array's reference count at run
  time; this function states neither. `ScidoniaInPlace`'s address assertions and
  the benchmark beside them are measurements of it.

* `nestedSet` on `Array (Array UInt64)` is `SealedStateVar.setLeaf` at an
  `ObsPath` of two steps. The type is a sealed state variable because it *is* the
  nested array layout's state type, so the write is the library's take-out update
  and the library's read is the only read the type has: a client cannot be handed
  the inner array. Each level costs one slot — O(1) — when it is exclusively
  owned, and copies its whole buffer when a live reference reaches it: the outer
  buffer for the take-out, the inner array for the write inside it.

* `treeSet` on a struct tree of depth `k` is `SealedStateVar.setLeaf` at an
  `ObsPath` of depth `k`. `structTree k` is `k` levels of `Layout.struct` over
  `Layout.leaf .uint`, so the state type is a nested pair with `2^k` leaves, and no
  user-declared structure is involved: `SealedStateVar.rep` is `rfl` because
  `Layout5.State (structTree k)` is the layout's own state type.

The complexity statements, stated honestly:

* `arrSet` is O(1) in place and O(n) on a copy, `n` the array's size.
* `nestedSet` is two steps, and each step is O(1) in place and copies its whole
  buffer when the level it is at is shared.
* `treeSet` **walks** the path. Its traversal is O(depth) = O(log n) whether or
  not the tree is exclusively owned, where `n = 2^k` is the number of leaves. What
  the ownership discipline changes is the *allocation*: with the tree exclusively
  owned the compiler's reset/reuse pass rewrites each struct cell along the path in
  place (O(1) allocation), and with a live reference to the tree every cell on the
  path is rebuilt (O(log n) allocation). The in-place update of a deep tree is
  therefore **not** O(1) overall, and nothing here claims it is.

Every claim about a machine — which cell kept its address, how long an update
took — is measured by `ScidoniaInPlace`, not proved here. What this module states
is which object a write rebuilds.
-/
import Scidonia.FracPerm.StateVar.Sealed

namespace ScidoniaExamples.Updates

open Scidonia.FracPerm.StateVar

/-! ## The flat array

An array of machine words is the object the interface threads, whole: no part of
it is hidden, and the update is the array primitive itself. The kernel cannot
reduce `Array`'s primitives on a literal, so the statements this module and the
checks make about concrete arrays are evaluations (`ScidoniaTest/Updates.lean`
uses `#guard` for them, and the take-out's own checks take the read as a
hypothesis for the same reason). -/

/-- Set the machine word at `i` to `v`, where `i` addresses a slot of the array.

The compiled write updates the array's buffer in place when the array is
exclusively owned — one slot, O(1) — and replaces it with a copy of the whole
buffer, O(n), when a second reference to it is live. Which one happens is the
array's reference count at run time, and this function states neither.

An out-of-bounds `i` is a caller error rather than a no-op: compiled, `Array.set!`
is `lean_array_set`, which panics on an index past the end. Its logical body,
`Array.setIfInBounds`, leaves the array alone instead, and the frame theorem in
`ScidoniaTest/Updates.lean` is stated about that body; the harness and the checks
below write only to slots the arrays have. -/
def arrSet (a : Array UInt64) (i : Nat) (v : UInt64) : Array UInt64 :=
  a.set! i v

/-! ## The nested array

The write is the sealed class's: the instance supplies the layout the type is and
the equality `rep`, and the library supplies the take-out, the two checks and the
put-back. A read through the same class returns an `Option Value` of the closed
observation universe, so the inner array a `setLeaf` takes out is never handed
back to a client. -/

/-- The path `.index i (.index j .here)` at the nested-array layout: the word at
slot `j` of the inner array at index `i`. -/
def nestedPath (i j : Nat) : Layout5.ObsPath SealedStateVar.sealedNested :=
  ⟨.index i (.index j .here), .uint, rfl⟩

/-- Set the word at slot `j` of the inner array at index `i` of `a`, reporting
whether the path addressed anything.

The sealed instance supplies the layout `Array (Array UInt64)` is, so this is the
library's take-out update: O(1) at each of the two levels when that level is
exclusively owned, and a whole-buffer copy at a level a live reference reaches. -/
def nestedSet (a : Array (Array UInt64)) (i j : Nat) (v : UInt64) :
    Array (Array UInt64) × Bool :=
  SealedStateVar.setLeaf (σ := Array (Array UInt64)) (nestedPath i j) v a

/-! ## The struct tree

`structTree k` is a full binary tree of structs: `k` levels of `Layout.struct`
over `Layout.leaf .uint`. Its state type is a nested pair, and it is sealed by
`rep` being `rfl` — the class's equality holds definitionally because the state
type is the layout's, which is why no user-declared structure is needed and why
the cast a sealed write performs erases.

A write at a leaf walks `k` struct cells and rewrites one word. The walk costs
O(depth) either way. The *allocation* is what the ownership discipline decides:
exclusively owned, the reset/reuse pass rewrites each pair cell the recursion
rebuilds in place, so the write allocates nothing for the spine (O(1)
allocation); with a live reference to the tree, each cell on the path is built
afresh (O(log n) allocation). -/

/-- The layout of the full binary struct tree of depth `k`: `k` levels of
`Layout.struct` over `Layout.leaf .uint`. Its state type is a nested pair with
`2^k` machine-word leaves, so a leaf path has depth `k` and the tree has `log₂`
as many leaves as it has levels. -/
def structTree : Nat → Layout5.Layout
  | 0 => .leaf .uint
  | k + 1 => .struct (structTree k) (structTree k)

/-- `Layout5.State (structTree k)` is a sealed state variable: the class's layout
is `structTree k` and its equality is `rfl`, because the type *is* that layout's
state type. Nothing else is supplied — the class has no field for a read, a write
or an encoding. -/
instance structTreeSealed (k : Nat) : SealedStateVar (Layout5.State (structTree k)) :=
  ⟨structTree k, rfl⟩

/-- The all-left path of depth `k`, as a path: the leftmost leaf of the tree. -/
def treeSteps : (k : Nat) → Layout5.Path (structTree k)
  | 0 => .here
  | k + 1 => .left (treeSteps k)

/-- Every all-left path ends at the machine-word leaf, whatever the depth: the
step adds a `left` to both the path and the layout at its end. -/
theorem treeSteps_leaf (k : Nat) : Layout5.At (treeSteps k) = .leaf .uint := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- The all-left path of depth `k` as a read path: the leftmost leaf of the tree.
The observation description is written `.uint` here rather than taken from the
recursion, which is what lets a write at this path carry a `UInt64` at every
depth. -/
def treePath (k : Nat) : Layout5.ObsPath (structTree k) :=
  ⟨treeSteps k, .uint, treeSteps_leaf k⟩

/-- The all-left path of depth `k` followed by one right step, as a path: the
sibling leaf, inside the deepest struct the all-left path passes through, of the
leftmost leaf. Its depth is `k + 1`, and it is disjoint from `treeSteps (k + 1)`. -/
def treeSiblingSteps : (k : Nat) → Layout5.Path (structTree (k + 1))
  | 0 => .right .here
  | k + 1 => .left (treeSiblingSteps k)

/-- Every sibling path ends at the machine-word leaf: one `right` step followed by
`left` steps, none of which changes the leaf. -/
theorem treeSiblingSteps_leaf (k : Nat) :
    Layout5.At (treeSiblingSteps k) = .leaf .uint := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- The sibling path as a read path. -/
def treeSiblingPath (k : Nat) : Layout5.ObsPath (structTree (k + 1)) :=
  ⟨treeSiblingSteps k, .uint, treeSiblingSteps_leaf k⟩

/-- The two paths are disjoint: they descend into the left and the right
component of the deepest struct the all-left path passes through, and above that
struct the two paths take the same `left` step. -/
theorem treePath_disjoint_sibling (k : Nat) :
    Layout5.Disjoint (treeSteps (k + 1)) (treeSiblingSteps k) := by
  induction k with
  | zero => exact Layout5.disjoint_left_right _ _
  | succ k ih => exact (Layout5.disjoint_left_iff).mpr ih

/-- The tree of depth `k` whose leaves hold `base` upwards from left to right: the
left subtree holds `base` to `base + 2^k - 1` and the right one the next `2^k`
values. The leftmost leaf holds `base`, and the sibling leaf `treeSiblingPath k`
holds `base + 1`. -/
def treeFilled : (k : Nat) → UInt64 → Layout5.State (structTree k)
  | 0, base => base
  | k + 1, base => (treeFilled k base, treeFilled k (base + (2 ^ k : Nat).toUInt64))

/-- Set the word at the leftmost leaf of a depth-`k` tree, reporting whether the
path addressed anything.

The write is `SealedStateVar.setLeaf` at a path of depth `k`, so the traversal
walks `k` struct cells and rewrites one word: O(depth) either way. What the
ownership discipline decides is the allocation of the spine — O(1) when the tree
is exclusively owned, O(log n) when a live reference makes it shared. -/
def treeSet (k : Nat) (v : UInt64) (t : Layout5.State (structTree k)) :
    Layout5.State (structTree k) × Bool :=
  SealedStateVar.setLeaf (σ := Layout5.State (structTree k)) (treePath k) v t

end ScidoniaExamples.Updates
