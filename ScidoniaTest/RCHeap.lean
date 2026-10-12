/-
Compile-time checks for `Scidonia.FracPerm.StateVar.RCHeap`.

The module is a counted heap: a cell carries the references its slots hold and the
count the runtime keeps for it, `Counted` ties that count to the aliasing
`Footprint` counts, and the update's two branches are the model of the write's
destructive and copying cases. A proof module has no pre-fix behaviour to
observe, so the checks here meet its definitions and theorems from outside, on
heaps a client of the module can build. They are of seven kinds:

* **The heap's invariants**, at the heaps below: the references each lists are
  duplicate-free and no listed cell carries a count of zero, and a heap that lists
  one reference twice fails the first. That refusal is what rules out the heap
  whose two cells at a reference disagree about the count: it is not a heap with a
  theorem missing, it is not a heap these theorems are stated about.
* **The counts themselves**, as `#guard`s of evaluated results on small heaps: the
  count of an exclusively owned cell, the count of a cell a second handle names,
  a count an allocation begins with, a count an increment raises and a count a
  non-final decrement lowers. Each detector has an affirmative control beside it —
  a false equation of the same `#guard` shape whose message is pinned — so a guard
  is shown to fire rather than to pass whatever it is given.
* **The update's two branches**, as `#guard`s of the location the updated slots
  are read back at: at a count of one the write keeps the location, and at a count
  of two the updated slots land at a fresh one while the old cell keeps its own.
* **Negative controls** as theorems about specific heaps: the cell a second handle
  names is not exclusive, the update at that cell does not land the write's slots
  at its location, and the update at the take-out pair's carried cell does not
  land them at the carried cell's location. Each stands beside an affirmative
  control at the *same* heap and handle list — the exclusive root of the same heap
  and handle list, and the fresh location the same update's slots land at — so the
  negative is about the reference and not about the heap being rejected
  everywhere.
* **Affirmative structural controls**: the heaps are counted by way of
  `counted_of`, the operations' preservation theorems build a heap that is
  `Counted`, live and duplicate-free from one that is, and `counted_iff_exclusive`,
  `counted_cell_count`, `update_preserves_location_of_exclusive` and
  `update_copies_of_shared` are applied at those heaps.
* **The take-out pair and the release**, at the counted heap: the pair's carried
  cell is not exclusive and a decrement of the pair's handle makes it exclusive
  again; and the last handle's release removes the cell and drops the references
  its slots held, so the heap it returns lists no count-zero cell and no
  occurrence of a cell it freed.
* **Axioms**: each representative theorem's `#print axioms` output is pinned to
  the standard kernel principles, so a proof that acquires any other axiom fails
  the build rather than printing a longer list for a reader to notice.

The heaps below are read as exactly the cells they list, which is the reading
`Counted` is stated under; nothing here constructs a heap from a program.
-/
import Scidonia.FracPerm.StateVar.RCHeap

open Scidonia.FracPerm.StateVar
open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap

namespace ScidoniaTest.RCHeap

/-! ## The heaps the checks are read at -/

/-- One cell, named by no slot and by the one handle that owns it. -/
def leafHeap : CHeap := [(1, { slots := [], count := 1 })]

/-- A chain of two cells: the root's one slot names the leaf, the leaf's slots name
nothing, and the one handle names the root. Every cell's count is one. -/
def chain : CHeap := [(0, { slots := [1], count := 1 }), (1, { slots := [], count := 1 })]

/-- The same chain with a second handle on the leaf: the leaf's count is two, so
the leaf is not exclusively owned. -/
def shared : CHeap := [(0, { slots := [1], count := 1 }), (1, { slots := [], count := 2 })]

/-- The cell a take-out's pair carries: it is named by no slot and by the pair's
two handles, which is what its count of two is. -/
def pairHeap : CHeap := [(0, { slots := [], count := 2 })]

/-- The cell a take-out's pair carries when its slots name a cell: the pair's two
handles make the carried cell's count two, and its one slot names the leaf. The
update at the carried cell is the case whose slots are read back at a location
other than the carried cell's own. -/
def pairCarrying : CHeap := [(0, { slots := [1], count := 2 }), (1, { slots := [], count := 1 })]

/-- The heap a duplicate reference is written into: both cells carry the reference
`0`, so the heap lists it twice. It is the counterexample the invariant rules out —
and the second cell's count of ninety-nine is what would otherwise escape
`Counted`, which reads only the first cell at a reference. -/
def duplicateKey : CHeap := [(0, { slots := [], count := 1 }), (0, { slots := [], count := 99 })]

/-! ## The invariants at these heaps

Each heap below is duplicate-free and carries no counted-zero cell, which is the
hypothesis the module's semantic theorems are stated under. `CHeap.Live` is the
form the cascade's own stopping test has, so the two are decidable at a concrete
heap. -/

/-- The leaf's heap is duplicate-free. -/
theorem leafHeap_wf : CHeap.WF leafHeap := by rw [CHeap.WF]; decide

/-- The leaf's heap carries no counted-zero cell. -/
theorem leafHeap_live : CHeap.Live leafHeap := by rw [CHeap.Live]; decide

/-- The chain is duplicate-free. -/
theorem chain_wf : CHeap.WF chain := by rw [CHeap.WF]; decide

/-- The chain carries no counted-zero cell. -/
theorem chain_live : CHeap.Live chain := by rw [CHeap.Live]; decide

/-- The chain with a second handle is duplicate-free. -/
theorem shared_wf : CHeap.WF shared := by rw [CHeap.WF]; decide

/-- The chain with a second handle carries no counted-zero cell. -/
theorem shared_live : CHeap.Live shared := by rw [CHeap.Live]; decide

/-- The pair's heap is duplicate-free. -/
theorem pair_wf : CHeap.WF pairHeap := by rw [CHeap.WF]; decide

/-- The pair's heap carries no counted-zero cell. -/
theorem pair_live : CHeap.Live pairHeap := by rw [CHeap.Live]; decide

/-- The pair's carried cell with its slot is duplicate-free. -/
theorem pairCarrying_wf : CHeap.WF pairCarrying := by rw [CHeap.WF]; decide

/-- The pair's carried cell with its slot carries no counted-zero cell. -/
theorem pairCarrying_live : CHeap.Live pairCarrying := by rw [CHeap.Live]; decide

/-- The chain is a heap the theorems that need both invariants at once are stated
about: duplicate-free and live. -/
theorem chain_healthy : CHeap.Healthy chain := ⟨chain_wf, chain_live⟩

/-- The chain with a second handle is such a heap. -/
theorem shared_healthy : CHeap.Healthy shared := ⟨shared_wf, shared_live⟩

/-- The pair's carried cell with its slot is such a heap. -/
theorem pairCarrying_healthy : CHeap.Healthy pairCarrying := ⟨pairCarrying_wf, pairCarrying_live⟩

/-! ## The counterexample the invariant rules out

The heap that lists one reference twice fails the invariant, whatever its cells'
counts say. This is the statement the module's own reading needs: the two cells at
reference `0` disagree, and `Counted` is stated at a reference and reads the first
of them, so nothing under `Counted` alone would make them agree. There is no
duplicate-free, counted heap whose cells at one reference disagree:
`counted_cell_count` reads every listed cell's own count. -/

/-- The heap that lists reference `0` twice is not one the invariant admits. -/
theorem duplicateKey_not_wf : ¬ CHeap.WF duplicateKey := by rw [CHeap.WF]; decide

/-- No heap that lists reference `0` twice is counted: the invariant's failure is
what an appeal to `Counted` at this heap would meet first. -/
theorem duplicateKey_not_counted : ¬ (CHeap.WF duplicateKey ∧ Counted duplicateKey [0]) :=
  fun h => duplicateKey_not_wf h.1

/-- The two cells at reference `0` carry counts of one and ninety-nine: the numbers
`Counted` alone would not have to reconcile, because it reads the first cell at a
reference and never the second. -/
theorem duplicateKey_counts : duplicateKey.map (fun e => e.2.count) = [1, 99] := by decide

/-! ## Counting a heap by hand

`Counted` is a statement about every reference, so a small heap is counted by
hand: its cells' counts are read off the occurrences and the handles, and the
heaps here are closed — every slot names a cell they list and every handle names
one — which is what lets the reference the heap does not list be discharged. -/

/-- A heap is counted when every cell it lists carries the count its occurrences
and its handles give it, every slot names a cell it lists, and every handle names
one. These are the three conditions a reader can check at a small heap. -/
theorem counted_of (c : CHeap) (handles : List Ref)
    (hcount : ∀ x ∈ CHeap.refs c, CHeap.count c x = (CHeap.slots c).count x + handles.count x)
    (hslot : ∀ x ∈ CHeap.slots c, x ∈ CHeap.refs c)
    (hhandle : ∀ x ∈ handles, x ∈ CHeap.refs c) : Counted c handles := by
  rw [counted_iff_slots]
  intro x
  by_cases hx : x ∈ CHeap.refs c
  · exact hcount x hx
  · have hs0 : (CHeap.slots c).count x = 0 :=
      List.count_eq_zero.mpr (fun hmem => hx (hslot x hmem))
    have hh0 : handles.count x = 0 :=
      List.count_eq_zero.mpr (fun hmem => hx (hhandle x hmem))
    rw [CHeap.count_eq_zero_of_not_mem hx, hs0, hh0]

/-- The leaf's own heap is counted at the one handle that owns it. -/
theorem leafHeap_counted : Counted leafHeap [1] := by
  refine counted_of leafHeap [1] ?_ ?_ ?_
  · intro x hx
    have hx' : x = 1 := by simpa [leafHeap] using hx
    subst hx'
    decide
  · intro x hx
    simp [leafHeap] at hx
  · intro x hx
    have hx' : x = 1 := by simpa [leafHeap] using hx
    subst hx'
    decide

/-- The chain is counted at the one handle that names its root. -/
theorem chain_counted : Counted chain [0] := by
  refine counted_of chain [0] ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 := by simpa [chain] using hx
    rcases hx' with rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 1 := by simpa [chain] using hx
    subst hx'
    decide
  · intro x hx
    have hx' : x = 0 := by simpa [chain] using hx
    subst hx'
    decide

/-- The chain with a second handle on the leaf is counted at both handles. -/
theorem shared_counted : Counted shared [0, 1] := by
  refine counted_of shared [0, 1] ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 := by simpa [shared] using hx
    rcases hx' with rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 1 := by simpa [shared] using hx
    subst hx'
    decide
  · intro x hx
    have hx' : x = 0 ∨ x = 1 := by simpa [shared] using hx
    rcases hx' with rfl | rfl <;> decide

/-- The pair's heap is counted at the pair's two handles. -/
theorem pair_counted : Counted pairHeap [0, 0] := by
  refine counted_of pairHeap [0, 0] ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 := by simpa [pairHeap] using hx
    subst hx'
    decide
  · intro x hx
    simp [pairHeap] at hx
  · intro x hx
    have hx' : x = 0 := by simpa [pairHeap] using hx
    subst hx'
    decide

/-! ## The counts, evaluated

Every `#guard` below is answered by an affirmative control: a false equation of
the same shape whose reported message is pinned, so the guard is shown to fire and
not to pass whatever it is given. -/

/-
The exclusive cell's count is one: the root is named by no slot and by the one
handle, so its count is one.
-/
#guard decide (CHeap.count chain 0 = 1)

/--
error: Expression
  decide (chain.count 0 = 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (CHeap.count chain 0 = 2)

/-
The cell a second handle names has count two: the leaf's one slot occurrence and
the second handle are two names.
-/
#guard decide (CHeap.count shared 1 = 2)

/--
error: Expression
  decide (shared.count 1 = 1)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (CHeap.count shared 1 = 1)

/-
An allocation begins at count one, whichever handle list the heap was counted at.
-/
#guard decide (CHeap.count (alloc leafHeap [1] 0 []).1 0 = 1)

/--
error: Expression
  decide ((alloc leafHeap [1] 0 []).fst.count 0 = 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (CHeap.count (alloc leafHeap [1] 0 []).1 0 = 2)

/-
The runtime's increment raises the count of the reference it names to two, and the
handle list it returns holds that reference twice.
-/
#guard decide (CHeap.count (dup chain [0] 0).1 0 = 2)
#guard decide ((dup chain [0] 0).2 = [0, 0])

/--
error: Expression
  decide ((dup chain [0] 0).fst.count 0 = 1)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (CHeap.count (dup chain [0] 0).1 0 = 1)

/-
The runtime's non-final decrement lowers the count by the one handle it takes out,
and it cannot free the cell: a heap whose count stands at one is not one it is
applied to.
-/
#guard decide (CHeap.count (decRef (dup chain [0] 0).1 [0, 0] 0).1 0 = 1)
#guard decide ((decRef (dup chain [0] 0).1 [0, 0] 0).2 = [0])

/--
error: Expression
  decide ((decRef (dup chain [0] 0).fst [0, 0] 0).fst.count 0 = 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (CHeap.count (decRef (dup chain [0] 0).1 [0, 0] 0).1 0 = 2)

/-
The exclusive cell's update keeps its location: the write's slots are read back at
the same reference, and the leaf the old slots named is freed — its one
occurrence gone, its count zero — so the heap it leaves lists no cell there.
-/
#guard decide ((update chain [0] 0 []).1.lookup 0 = some [])
#guard decide ((update chain [0] 0 []).1.count 1 = 0)

/--
error: Expression
  decide ((update chain [0] 0 []).fst.lookup 0 = some [1])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((update chain [0] 0 []).1.lookup 0 = some [1])

/-
The cell a second handle names copies: the updated slots are read back at the
fresh location beyond every reference the heap lists, while the old cell keeps its
own slots.
-/
#guard decide ((update shared [0, 1] 1 []).1.lookup 2 = some [])
#guard decide ((update shared [0, 1] 1 []).1.lookup 1 = CHeap.lookup shared 1)

/--
error: Expression
  decide ((update shared [0, 1] 1 []).fst.lookup 2 = some [1])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((update shared [0, 1] 1 []).1.lookup 2 = some [1])

/-
The pair's carried cell: two handles to a cell no slot names are two live
references, and one handle is one.
-/
#guard decide (refCount (CHeap.presentation pairHeap) [0, 0] 0 ≠ 1)
#guard decide (refCount (CHeap.presentation pairHeap) [0] 0 = 1)

/--
error: Expression
  decide (refCount pairHeap.presentation [0, 0] 0 = 1)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (refCount (CHeap.presentation pairHeap) [0, 0] 0 = 1)

/-! ## Negative controls, their affirmative counterparts, and the take-out pair

The specific heaps whose obligation is false, each beside an affirmative control
at the *same* heap and handle list, so the negative is about the reference and not
about the heap. The take-out pair is then read at the counted heap: the carried
cell is not exclusive, a decrement of the pair's handle makes it exclusive, and
the update at it copies while the pair holds it. -/

/-- The cell the second handle names is not exclusive: the slot occurrence and the
second handle are two live references.

Its affirmative counterpart is `shared_root_exclusive` at the root of the *same*
heap and the *same* handle list, whose one handle is one live reference. -/
theorem shared_not_exclusive : ¬ Exclusive (CHeap.presentation shared) [0, 1] 1 := by
  intro h
  have h1 : CHeap.count shared 1 = 1 := (counted_iff_exclusive shared_counted 1).mpr h
  rw [show CHeap.count shared 1 = 2 from by decide] at h1
  omega

/-- The root of that same heap, at the same handle list, is exclusive: no slot
names it and the one handle that does is one live reference.

This is the affirmative control the negative above is read against — the same heap,
the same two handles, and the reference the two handles leave exclusive. -/
theorem shared_root_exclusive : Exclusive (CHeap.presentation shared) [0, 1] 0 :=
  (counted_iff_exclusive shared_counted 0).mp (by decide)

/-- The update at the cell the second handle names does not land its slots at that
cell's location: the write goes to the fresh location instead, and the aliased cell
keeps the slots it had.

Its affirmative counterpart is `shared_update_at_fresh`, which reads the same
write's slots back at that fresh location at the same heap. -/
theorem shared_update_not_at_leaf : (update shared [0, 1] 1 [0]).1.lookup 1 ≠ some [0] := by
  decide

/-- The updated slots of the same write, read at the fresh location: the copy is
where the write landed, which is the affirmative control beside
`shared_update_not_at_leaf`. -/
theorem shared_update_at_fresh : (update shared [0, 1] 1 [0]).1.lookup 2 = some [0] := by
  decide

/-- The take-out pair's carried cell is not exclusive: the pair's two handles are
two live references, whatever the heap names.

Its affirmative counterpart is `pair_dropped_exclusive`, the same heap after a
decrement of the pair's handle. -/
theorem pair_not_exclusive : ¬ Exclusive (CHeap.presentation pairHeap) [0, 0] 0 :=
  (takeout_pair_count_two pair_counted (by decide)).2

/-- The pair's count is two, read at the heap's own field: the value a write tests
at the element is the count the pair's second handle raised. -/
theorem pair_count_two : CHeap.count pairHeap 0 = 2 :=
  (takeout_pair_count_two pair_counted (by decide)).1

/-- A decrement of the pair's handle makes the carried cell exclusive again. -/
theorem pair_dropped_exclusive :
    Exclusive (CHeap.presentation (decRef pairHeap [0, 0] 0).1) (decRef pairHeap [0, 0] 0).2 0 :=
  (takeout_dropped_count_one pair_counted (by decide)).2

/-- The pair at the update's decision: with the pair's handle held the update at
the element copies, and with the handle released first the same update keeps the
location. -/
theorem pair_update_branches :
    (update pairHeap [0, 0] 0 []).1.lookup (fresh pairHeap []) = some [] ∧
      (update (decRef pairHeap [0, 0] 0).1 (decRef pairHeap [0, 0] 0).2 0 []).1.lookup 0
        = some [] :=
  takeout_pair_update_branches pair_wf pair_counted (by decide) (by decide)

/-! ### The pair's carried cell when its slots name a cell

The pair above carries a cell whose slots name nothing, so the write's slots and
the cell's own are both empty and no location distinguishes them. `pairCarrying`
carries a cell whose one slot names the leaf, which is the case where the update is
read at two different locations. -/

/-- The pair's carried cell with its slot is counted at the pair's two handles: the
carried cell's count is its two handles, and the leaf's is the one occurrence the
carried cell's slot contributes. -/
theorem pairCarrying_counted : Counted pairCarrying [0, 0] := by
  refine counted_of pairCarrying [0, 0] ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 := by simpa [pairCarrying] using hx
    rcases hx' with rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 1 := by simpa [pairCarrying] using hx
    subst hx'
    decide
  · intro x hx
    have hx' : x = 0 := by simpa [pairCarrying] using hx
    subst hx'
    decide

/-- The pair's carried cell at this heap is not exclusive either: the module's pair
theorem reads the two handles there as it does at the pair's own heap. -/
theorem pairCarrying_not_exclusive :
    ¬ Exclusive (CHeap.presentation pairCarrying) [0, 0] 0 :=
  (takeout_pair_count_two pairCarrying_counted (by decide)).2

/-- The update at the pair's carried cell does not land its slots at the carried
cell's location: its count of two sends the write to the copying branch, so the
updated slots are read back at the fresh location and the carried cell keeps the
slot it had.

Its affirmative counterpart is `pairCarrying_update_at_fresh`, which reads the same
write's slots back at that fresh location at the same heap. -/
theorem pairCarrying_update_not_at_self :
    (update pairCarrying [0, 0] 0 []).1.lookup 0 ≠ some [] := by
  decide

/-- The updated slots of the same write, read at the fresh location: the copy is
where the write landed, which is the affirmative control beside
`pairCarrying_update_not_at_self`. -/
theorem pairCarrying_update_at_fresh :
    (update pairCarrying [0, 0] 0 []).1.lookup (fresh pairCarrying []) = some [] := by
  decide

/-- The copying branch at the pair's carried cell, at one call: the updated slots
are at a fresh location, the carried cell keeps its slots, its count has fallen by
one, and the fresh location is not one the heap listed. -/
theorem pairCarrying_update_copies :
    (update pairCarrying [0, 0] 0 []).1.lookup (fresh pairCarrying []) = some [] ∧
      (update pairCarrying [0, 0] 0 []).1.lookup 0 = CHeap.lookup pairCarrying 0 ∧
      (update pairCarrying [0, 0] 0 []).1.count 0 = CHeap.count pairCarrying 0 - 1 ∧
      fresh pairCarrying [] ∉ CHeap.refs pairCarrying :=
  update_copies_of_shared pairCarrying_counted pairCarrying_not_exclusive (r := 0) (ks := [])
    (by decide) (by decide)

/-
The pair's two states as evaluated results, each with its own control, and the
same two locations at the carried cell whose slots name a leaf.
-/
#guard decide ((update pairHeap [0, 0] 0 []).1.lookup (fresh pairHeap []) = some [])
#guard decide ((update (decRef pairHeap [0, 0] 0).1 (decRef pairHeap [0, 0] 0).2 0 []).1.lookup 0
  = some [])

/--
error: Expression
  decide ((update pairHeap [0, 0] 0 []).fst.lookup (fresh pairHeap []) = some [1])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((update pairHeap [0, 0] 0 []).1.lookup (fresh pairHeap []) = some [1])

/--
error: Expression
  decide ((update (decRef pairHeap [0, 0] 0).fst (decRef pairHeap [0, 0] 0).snd 0 []).fst.lookup 0 = some [1])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((update (decRef pairHeap [0, 0] 0).1 (decRef pairHeap [0, 0] 0).2 0 []).1.lookup 0
  = some [1])

/-! ## The operations' preservation, and the bridge, at these heaps

Each theorem is exercised at a concrete heap: the counts above are met by a heap
the module's own operations built from a counted one, so the preservation theorems
are applied and not only read. -/

/-- The leaf an allocation of the root extends: one cell named by no slot. -/
theorem allocLeaf_counted : Counted (alloc leafHeap [1] 0 []).1 (alloc leafHeap [1] 0 []).2 :=
  counted_alloc leafHeap_counted (r := 0) (ks := []) (by decide) (by decide)
    (by intro x hx; simp at hx)

/-- The allocation's heap is duplicate-free as well: the new reference was not one
the heap listed. -/
theorem allocLeaf_wf : CHeap.WF (alloc leafHeap [1] 0 []).1 :=
  CHeap.wf_alloc leafHeap_wf (by decide)

/-- The increment's heap is counted: the handle it adds and the count it raises
name the same reference. -/
theorem dup_counted : Counted (dup chain [0] 0).1 (dup chain [0] 0).2 :=
  counted_dup chain_counted (r := 0) (by decide)

/-- The increment's heap is duplicate-free and carries no counted-zero cell. -/
theorem dup_wf : CHeap.WF (dup chain [0] 0).1 := CHeap.wf_dup chain_wf

/-- The increment's heap carries no counted-zero cell. -/
theorem dup_live : CHeap.Live (dup chain [0] 0).1 := CHeap.live_dup chain_healthy (by decide)

/-- The non-final decrement's heap is counted at the handle list it returns. -/
theorem decRef_counted :
    Counted (decRef (dup chain [0] 0).1 [0, 0] 0).1 (decRef (dup chain [0] 0).1 [0, 0] 0).2 :=
  counted_decRef dup_counted (r := 0) (by decide)

/-- The bridge at the chain's root, read from the heap's own count: a count of one
and `Footprint`'s exclusivity are the same statement there. -/
theorem chain_count_iff_exclusive :
    CHeap.count chain 0 = 1 ↔ Exclusive (CHeap.presentation chain) [0] 0 :=
  counted_iff_exclusive chain_counted 0

/-- The chain's root is exclusive under the one handle that names it. -/
theorem chain_root_exclusive : Exclusive (CHeap.presentation chain) [0] 0 :=
  (chain_count_iff_exclusive).mp (by decide)

/-- The destructive branch at the chain's root: the write keeps the location, which
needs the write's own handle — the reason no cell's slots name the root. -/
theorem chain_update_keeps_location : (update chain [0] 0 []).1.lookup 0 = some [] :=
  update_preserves_location_of_exclusive chain_wf chain_counted chain_root_exclusive
    (r := 0) (ks := []) (by decide) (by decide)

/-- The copying branch at the aliased leaf, at one call: the updated slots are at a
fresh location, the old cell keeps its slots, its count has fallen by one, and the
fresh location is not one the heap listed. -/
theorem shared_update_copies :
    (update shared [0, 1] 1 []).1.lookup (fresh shared []) = some [] ∧
      (update shared [0, 1] 1 []).1.lookup 1 = CHeap.lookup shared 1 ∧
      (update shared [0, 1] 1 []).1.count 1 = CHeap.count shared 1 - 1 ∧
      fresh shared [] ∉ CHeap.refs shared :=
  update_copies_of_shared shared_counted shared_not_exclusive (r := 1) (ks := [])
    (by decide) (by decide)

/-- The destructive branch preserves `Counted`. -/
theorem chain_update_counted : Counted (update chain [0] 0 []).1 (update chain [0] 0 []).2 :=
  counted_update_exclusive chain_wf chain_counted chain_root_exclusive (by decide) (by decide)
    (by intro x hx; simp at hx)

/-- The destructive branch leaves a duplicate-free heap: the write keeps the
references and the cascade removes some. -/
theorem chain_update_wf : CHeap.WF (update chain [0] 0 []).1 := CHeap.wf_update chain_wf

/-- The destructive branch leaves no counted-zero cell: the write's own drop frees
the leaf rather than leaving it listed at zero. -/
theorem chain_update_live : CHeap.Live (update chain [0] 0 []).1 :=
  CHeap.live_update chain_healthy

/-- The copying branch preserves `Counted`. -/
theorem shared_update_counted : Counted (update shared [0, 1] 1 []).1 (update shared [0, 1] 1 []).2 :=
  counted_update_copy shared_counted shared_not_exclusive (r := 1) (ks := [])
    (by decide) (by decide) (by intro x hx; simp at hx)

/-- The copying branch leaves a duplicate-free heap: the fresh cell's location is
beyond every reference the heap lists. -/
theorem shared_update_wf : CHeap.WF (update shared [0, 1] 1 []).1 := CHeap.wf_update shared_wf

/-- The copying branch leaves no counted-zero cell: nothing it does lowers a count
below one. -/
theorem shared_update_live : CHeap.Live (update shared [0, 1] 1 []).1 :=
  CHeap.live_update shared_healthy

/-! ## The counts read at every cell

`counted_cell_count` is the statement the first-entry reading is not enough for:
every cell a heap lists carries its own aliasing count, not only the one the heap
reads first. These checks apply it at the heaps above, and read the counts the
cells actually carry — including the two the duplicate-key heap's cells carry, the
numbers the invariant refuses. -/

/-- Every cell the chain lists carries its aliasing count — the second cell's own
field as much as the first's. -/
theorem chain_cells_count_themselves (e : Ref × Cell) (he : e ∈ chain) :
    e.2.count = refCount (CHeap.presentation chain) [0] e.1 :=
  counted_cell_count chain_wf chain_counted he

/-- The same at the aliased heap: the leaf's own field is two, its one occurrence
plus the second handle. -/
theorem shared_cells_count_themselves (e : Ref × Cell) (he : e ∈ shared) :
    e.2.count = refCount (CHeap.presentation shared) [0, 1] e.1 :=
  counted_cell_count shared_wf shared_counted he

/-
The counts the cells carry, evaluated: one per cell in the chain, one and two in
the aliased heap, and one and ninety-nine in the duplicate-key heap the invariant
refuses.
-/
#guard decide (chain.map (fun e => e.2.count) = [1, 1])
#guard decide (shared.map (fun e => e.2.count) = [1, 2])
#guard decide (duplicateKey.map (fun e => e.2.count) = [1, 99])

/-
The invariant at these heaps, evaluated: the four heaps the checks are read at are
duplicate-free, and the duplicate-key heap is not — the refusal is what leaves its
cells' counts unreconciled.
-/
#guard decide ((CHeap.refs chain).Nodup)
#guard decide ((CHeap.refs shared).Nodup)
#guard decide ((CHeap.refs pairHeap).Nodup)
#guard decide ((CHeap.refs pairCarrying).Nodup)
#guard decide (¬ (CHeap.refs duplicateKey).Nodup)

/-
Liveness, evaluated at the two forms it has: the chain lists no cell with a count
of zero, and the heap a decrement at a count of one would leave does — the control
beside the liveness checks, so `Live`'s passage is shown not to be free.
-/
#guard decide ((chain.find? (fun e => e.2.count == 0)) = none)
#guard decide (¬ ((decRef leafHeap [1] 1).1.find? (fun e => e.2.count == 0) = none))

/--
error: Expression
  decide duplicateKey.refs.Nodup
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((CHeap.refs duplicateKey).Nodup)

/-! ## The release, and the heap it leaves

The runtime's drop is two operations in the module, and these checks read them
apart: a count that stands above one is only decremented, and the last handle's
release removes the cell and drops the references its slots held. What a release
leaves is checked for exactly what a live-cell heap needs — no listed cell whose
count is zero, and no occurrence of a reference the heap no longer lists. -/

/-- A heap that lists no cell with a count of zero, and whose slots name only cells
it lists: the two things a release's result is checked to have. -/
def swept (c : CHeap) : Bool :=
  c.all (fun e => decide (0 < e.2.count)) &&
    (CHeap.slots c).all (fun r => decide (r ∈ CHeap.refs c))

/-- The leaf's only handle released: the cell goes and the heap that remains is
empty. A mere decrement at a count of one would have left the cell listed with a
count of zero, which is the call `decRef`'s premise rules out. -/
theorem release_leafHeap : release leafHeap [1] 1 = ([], []) := by decide

/-- The chain's root released: the root goes, and the leaf its slot named is freed
by the same release, so the heap that remains is empty and no occurrence of the
leaf is left behind. -/
theorem release_chain : release chain [0] 0 = ([], []) := by decide

/-- The release drops the references the released cell held: the chain's one
occurrence of the leaf is gone, and the leaf itself with it. -/
theorem release_chain_drops_occurrence :
    (CHeap.slots (release chain [0] 0).1).count 1 = 0 ∧
      1 ∉ CHeap.refs (release chain [0] 0).1 := by
  refine ⟨by decide, by decide⟩

/-- The release at the root of the aliased heap: the root goes and the leaf its
slot named survives — its count falls by the occurrence the root held, and the
second handle keeps it above zero. -/
theorem release_shared :
    (release shared [0, 1] 0).1 = [(1, { slots := [], count := 1 })] ∧
      (release shared [0, 1] 0).2 = [1] := by
  refine ⟨by decide, by decide⟩

/-- The decrement the release is not: at a count of one the non-final decrement
would leave the leaf listed with a count of zero and no way to name it. -/
theorem decRef_at_one_would_leave_a_dead_cell :
    CHeap.count (decRef leafHeap [1] 1).1 1 = 0 ∧ 1 ∈ CHeap.refs (decRef leafHeap [1] 1).1 := by
  refine ⟨by decide, by decide⟩

/-- The detector beside the release checks, on the heap that decrement would leave:
the heap lists a cell with a count of zero, so the detector reports it — which is
what makes `swept`'s passage at the release's results worth reading. -/
theorem decRef_at_one_not_swept : swept (decRef leafHeap [1] 1).1 = false := by decide

/-- The release of the chain's root is counted at the handle list it returns. -/
theorem release_chain_counted : Counted (release chain [0] 0).1 (release chain [0] 0).2 :=
  counted_release chain_wf chain_counted (r := 0) (by decide) (by decide)

/-- The release of the aliased root is counted at the handle list it returns: the
leaf's surviving count is the handle it holds. -/
theorem release_shared_counted : Counted (release shared [0, 1] 0).1 (release shared [0, 1] 0).2 :=
  counted_release shared_wf shared_counted (r := 0) (by decide) (by decide)

/-- The release leaves a duplicate-free heap: the deallocation removes one
reference and the cascade removes the cells whose counts it brought to zero. -/
theorem release_chain_wf : CHeap.WF (release chain [0] 0).1 := CHeap.wf_release chain_wf

/-- The release leaves a live heap: no listed cell carries a count of zero. -/
theorem release_chain_live : CHeap.Live (release chain [0] 0).1 :=
  (release_live_and_freed chain_wf).1

/-- The released cell is not one the heap lists afterwards. -/
theorem release_chain_freed : CHeap.count (release chain [0] 0).1 0 = 0 :=
  (release_live_and_freed chain_wf).2

/-- The release's own cascade has stopped rather than run out: further steps leave
the heap it returns as it is, at the heap that still lists a cell as well as at the
empty one. -/
theorem release_stable :
    CHeap.cascadeSteps 4 (release shared [0, 1] 0).1 = (release shared [0, 1] 0).1 ∧
      CHeap.cascadeSteps 4 (release chain [0] 0).1 = (release chain [0] 0).1 := by
  refine ⟨by decide, by decide⟩

/-
The release's results as evaluated checks: the two heaps are empty, the occurrence
the release drops was in the chain's slots before it ran, the detector passes at the
heaps it leaves, and further cascade steps leave the surviving heap as it is.
-/
#guard decide (release chain [0] 0 = ([], []))
#guard decide (release leafHeap [1] 1 = ([], []))
#guard decide ((CHeap.slots chain).count 1 = 1)
#guard swept (release chain [0] 0).1
#guard swept (release leafHeap [1] 1).1
#guard swept (release shared [0, 1] 0).1
#guard decide (CHeap.cascadeSteps 4 (release shared [0, 1] 0).1
  = [(1, { slots := [], count := 1 })])

/--
error: Expression
  decide ((release chain [0] 0).fst = [(1, { slots := [], count := 0 })])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((release chain [0] 0).1 = [(1, { slots := [], count := 0 })])

/-! ## Axioms of representative theorems

The facts above are proved with `simp`, `omega`, `rw`, `decide` and the model's own
recursions, which are kernel-checked and add no axiom, so each must rest on
standard kernel principles and no others. These are asserted rather than printed:
each `#guard_msgs` pins the message `#print axioms` emits, so a proof that
acquires any axiom fails the build instead of printing a longer list for a reader
to notice. Whitespace is compared loosely, so what is pinned is the names, not the
line breaks they happen to wrap at. -/

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_iff_exclusive' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_iff_exclusive

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_iff_slots' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_iff_slots

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_alloc' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_alloc

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_dup' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_dup

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_decRef' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_decRef

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_cell_count' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_cell_count

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_dealloc_handle' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_dealloc_handle

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_cascade' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_cascade

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.CHeap.cascade_stable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CHeap.cascade_stable

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_release' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_release

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.CHeap.wf_update' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms CHeap.wf_update

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.CHeap.live_update' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CHeap.live_update

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.release_live_and_freed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms release_live_and_freed

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_writeSlots' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_writeSlots

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.update_preserves_location_of_exclusive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms update_preserves_location_of_exclusive

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.update_copies_of_shared' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms update_copies_of_shared

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_update_exclusive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_update_exclusive

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_update_copy' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_update_copy

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.takeout_pair_count_two' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms takeout_pair_count_two

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.takeout_dropped_count_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms takeout_dropped_count_one

/--
info: 'Scidonia.FracPerm.StateVar.RCHeap.takeout_pair_update_branches' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms takeout_pair_update_branches

/--
info: 'ScidoniaTest.RCHeap.counted_of' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_of

/--
info: 'ScidoniaTest.RCHeap.chain_counted' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chain_counted

/--
info: 'ScidoniaTest.RCHeap.chain_update_keeps_location' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chain_update_keeps_location

/--
info: 'ScidoniaTest.RCHeap.shared_update_copies' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms shared_update_copies

/--
info: 'ScidoniaTest.RCHeap.shared_update_not_at_leaf' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms shared_update_not_at_leaf

/--
info: 'ScidoniaTest.RCHeap.pair_not_exclusive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pair_not_exclusive

end ScidoniaTest.RCHeap
