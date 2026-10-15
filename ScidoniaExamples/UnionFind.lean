/-
A union-find over arrays of machine words: the example library's first
*algorithm* rather than a single update, and the canonical place where updating
in place instead of copying is the whole point of the program.

The algorithm is the ordinary one. `parent` and `rank` are `Array UInt64`; `find`
walks from an element to its root and halves the path on the way; `union` finds
both roots and links one under the other by rank. A union's amortized cost is
near-constant because the array is updated where it lies — and that is exactly
what a copy per write would destroy.

What is not ordinary is the write. Both arrays are states of the sealed class:
the layout is `.arr (.leaf .uint)`, whose state type *is* `Array UInt64`, so the
instance's `rep` is `rfl` and the cast a sealed write performs erases. Every write
below is `SealedStateVar.setLeaf` at a one-step `ObsPath` and not a bare
`Array.set!`, so each one is the library's take-out update: the addressed element
is exchanged with the layout's placeholder in an owned `Array.swapAt`, the new
word is put back in the slot, and the library's checks on the array and on the
extracted focus are the ones that run. This is the discipline the writes here
have, and it is the sealed class's — the ownership typing of `Scidonia.RC` is
about first-order expressions and does not reach this function.

The two runs differ in one thing: what else refers to the arrays while a step's
writes run.

* `runDisciplined` carries `parent` and `rank` as the recursion's parameters and
  holds nothing else, so a step's writes meet the only reference to each array and
  each take-out updates the buffer in place, O(1) per write.
* `runAliased` takes a second reference to both arrays at every step and reads it
  after that step's writes. That is the shape in which a step's first write meets
  a buffer another name reaches and replaces it with a copy — one whole-buffer
  copy per step per array, O(n) where the in-place write is O(1). The `seen` total
  this definition returns is those reads: it is what keeps them in the program,
  and it is not part of the partition. Which of the two shapes a *compiled* run of
  this definition takes is not something a definition fixes, since a pure read can
  be scheduled before the write it was meant to follow, so the copy is measured
  where the read is sequenced after the write instead: the `IO` loop of
  `ScidoniaInPlace`, whose aliased addresses move.

The partition is the same in both runs and the cost is not. Each side of that is
established by the instrument that can see it. `ScidoniaTest/UnionFind` compares
the two runs' partitions by evaluation. Which buffer kept its address, and how
long a union took, are observations of `ScidoniaInPlace`, which drives both shapes
as `IO` loops — the aliased one reading each alias through `addressIO` after the
step's writes, which is what keeps the reference alive across them — and asserts
the addresses and prints the times it measured. Nothing in this module states a
machine claim.
-/
import Scidonia.FracPerm.StateVar.Sealed

namespace ScidoniaExamples.UnionFind

open Scidonia.FracPerm.StateVar

/-! ## The flat array as a sealed state variable

A union-find's two arrays are flat arrays of machine words. That layout's state
type is `Array UInt64` definitionally — `State (.arr (.leaf .uint))` is
`Array (ObsEl .uint)`, and `ObsEl .uint` is `UInt64` — so the type is a sealed
state variable with `rep := rfl`: nothing is supplied but the layout and the
equality, and the read and the write are the library's. -/

/-- The layout of the sealed flat-array instance: an array of machine words. -/
abbrev sealedWords : Layout5.Layout := .arr (.leaf .uint)

/-- An array of machine words is a sealed state variable, with `rep := rfl`
because the type *is* the layout's state type. -/
instance : SealedStateVar (Array UInt64) := ⟨sealedWords, rfl⟩

/-- The path `.index i .here` at the flat-array layout: the word at slot `i`. -/
def wordPath (i : Nat) : Layout5.ObsPath sealedWords := ⟨.index i .here, .uint, rfl⟩

/-- Write `v` at slot `i` of the array, as the sealed class's take-out update at
`wordPath i` and no other operation: the library's write takes the element out of
the slot, checks the array and the extracted focus, installs the new word and puts
the focus back. On an exclusively owned array the two exchanges update the buffer
in place, O(1); on an array a live reference reaches, the first of them replaces
the buffer with a copy, O(n).

A slot the array does not have addresses nothing, and the write then reports
failure and leaves the state alone — which is why this helper can drop the
report: the algorithm below reads an index before it writes it. -/
def writeWord (a : Array UInt64) (i : Nat) (v : UInt64) : Array UInt64 :=
  (SealedStateVar.setLeaf (σ := Array UInt64) (wordPath i) v a).1

/-! ## The algorithm

`parent` and `rank` are two flat arrays. The reads below are `Array`'s own
borrowed read and not the sealed class's: a parent slot and a rank slot are
machine words, and this module's writes go through the sealed class alone. -/

/-- The parent an array records for the element `x`: the word at slot `x`, or `x`
itself when the index addresses no slot, which makes such an element its own
root. -/
def parentOf (parent : Array UInt64) (x : Nat) : Nat :=
  match parent[x]? with
  | some p => p.toNat
  | none => x

/-- The rank an array records for the element `x`: the word at slot `x`, or zero
when the index addresses no slot. -/
def rankOf (rank : Array UInt64) (x : Nat) : Nat :=
  match rank[x]? with
  | some r => r.toNat
  | none => 0

/-- The representative of the element `x`, with the parent array the walk left
behind: `find` with path halving.

One step reads `x`'s parent and, when `x` is not its own parent, sets `parent[x]`
to the parent of that parent — the write below, through the sealed class, the
take-out update of one slot — and continues from the grandparent, which is why the
walk visits every other element of the path.

`fuel` bounds the walk rather than a proof: a union-find's arrays are a forest
whose depth never exceeds the number of elements, so a caller that passes
`fuel = n` reaches the root, while an array that is not a forest keeps the walk to
`fuel` steps and reports the element it reached. -/
def find : Nat → Array UInt64 → Nat → Array UInt64 × Nat
  | 0, parent, x => (parent, x)
  | fuel + 1, parent, x =>
    let px := parentOf parent x
    if px = x then (parent, x)
    else
      let gx := parentOf parent px
      find fuel (writeWord parent x gx.toUInt64) gx

/-- Link the trees of the elements `x` and `y` by rank, with both arrays the
arrays the step left behind.

The two roots are found first, each find with its own path-halving writes. Roots
that agree leave the arrays alone — `x` and `y` are already in one set. Otherwise
the root of the lower rank is linked under the root of the higher one, which is
one write to `parent`; equal ranks are linked in one direction and the surviving
root's rank is raised, which is a second write, to `rank`. Linking by rank is what
keeps a tree's depth logarithmic, which is what keeps the next find short. -/
def union (fuel : Nat) (parent rank : Array UInt64) (x y : Nat) :
    Array UInt64 × Array UInt64 :=
  let (parent₁, rx) := find fuel parent x
  let (parent₂, ry) := find fuel parent₁ y
  if rx = ry then (parent₂, rank)
  else
    let rankX := rankOf rank rx
    let rankY := rankOf rank ry
    if rankX < rankY then (writeWord parent₂ rx ry.toUInt64, rank)
    else if rankY < rankX then (writeWord parent₂ ry rx.toUInt64, rank)
    else (writeWord parent₂ ry rx.toUInt64, writeWord rank rx (rankX + 1).toUInt64)

/-- The parent array of `n` elements, each its own root: `parent[i] = i`. -/
def singletons (n : Nat) : Array UInt64 :=
  (List.range n).toArray.map (fun i => i.toUInt64)

/-- The rank array of `n` fresh elements: `n` zeros, every element a tree of
depth zero. -/
def zeroRanks (n : Nat) : Array UInt64 :=
  (List.range n).toArray.map (fun _ => 0)

/-- The representative `find` reports for each element from `i` on, in order, with
the parent array the walks left behind. -/
def representativesFrom : Nat → Nat → Array UInt64 → Array Nat → Array UInt64 × Array Nat
  | 0, _, parent, roots => (parent, roots)
  | fuel + 1, i, parent, roots =>
    let (parent', r) := find fuel parent i
    representativesFrom fuel (i + 1) parent' (roots.push r)

/-- The partition a parent array describes, as `find` computes it: the
representative of each of the first `n` elements, in order, with the parent array
the walks left behind. Each walk is given `n` steps, which is more than a forest
of `n` elements is deep, and two elements are in one set exactly when their
representatives agree, every representative then being its own parent. -/
def representatives (n : Nat) (parent : Array UInt64) : Array UInt64 × Array Nat :=
  representativesFrom n 0 parent #[]

/-! ## The two runs

Both runs perform the same unions of the same list on the same two arrays. They
differ in what else refers to those arrays while a step's writes run, which is the
one thing a compiled write's cost depends on. -/

/-- The disciplined run of a list of unions: the two arrays are the recursion's
parameters and nothing else refers to them, so each step's writes meet the only
reference to each array and each take-out updates the buffer in place. -/
def runDisciplined : Nat → List (Nat × Nat) → Array UInt64 → Array UInt64 →
    Array UInt64 × Array UInt64
  | _, [], parent, rank => (parent, rank)
  | fuel, (x, y) :: rest, parent, rank =>
    let (parent', rank') := union fuel parent rank x y
    runDisciplined fuel rest parent' rank'

/-- The undisciplined run of the same unions: at every step a second reference to
both arrays is taken and read after that step's writes, and the reads are summed
into the `seen` total the run returns, so no read and no step is eliminated.

That is the shape in which a step's first write meets a buffer another name
reaches and replaces it with a copy. This definition fixes the shape's *value* —
the partition it computes is the one `runDisciplined` computes, which is what
`ScidoniaTest/UnionFind` compares — and not what a compiled run of the shape
costs: a pure read may be scheduled before the write it was meant to follow, so
the copy is measured where the read is sequenced after the write instead, in
`ScidoniaInPlace`'s `IO` loop of the same shape, whose address assertions and
times are the evidence. -/
def runAliased : Nat → List (Nat × Nat) → Array UInt64 → Array UInt64 →
    Array UInt64 × Array UInt64 × Nat
  | _, [], parent, rank => (parent, rank, 0)
  | fuel, (x, y) :: rest, parent, rank =>
    let aliasParent := parent
    let aliasRank := rank
    let (parent', rank') := union fuel parent rank x y
    let here := ((aliasParent[x]?).map UInt64.toNat).getD 0
      + ((aliasRank[y]?).map UInt64.toNat).getD 0
    let (parent'', rank'', seen) := runAliased fuel rest parent' rank'
    (parent'', rank'', seen + here)

/-! ## The sequence the harness runs

A fixed sequence of unions rather than a random one, so that every row of the
measurement and every run of the cases performs the same work on the same
elements. -/

/-- A fixed sequence of `ops` unions over `n` elements: the `i`-th joins element
`i % n` to element `(i + n / 2) % n`. It is a value, so the same unions run in
every measurement and every run. A pair's two elements differ whenever `n` holds
at least two of them, so the first union links two roots and writes. -/
def schedule (n ops : Nat) : List (Nat × Nat) :=
  (List.range ops).map (fun i => (i % n, (i + n / 2) % n))

/-- The number of elements the small union-find cases and checks run on: eight,
which holds a schedule whose sets are not all singletons. -/
def smallElements : Nat := 8

/-- The small concrete union sequence the cases and the checks run: with
`smallElements` elements, these four unions leave the sets `{0, 1, 2, 3}`,
`{4, 5}`, `{6}` and `{7}`. -/
def smallSchedule : List (Nat × Nat) := [(0, 1), (2, 3), (4, 5), (0, 2)]

end ScidoniaExamples.UnionFind
