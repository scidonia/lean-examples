/-
Compile-time checks for `Scidonia.FracPerm.StateVar.RCHeap`.

The module is a counted heap: a cell carries the references its slots hold and the
count the runtime keeps for it, `Counted` ties that count to the aliasing
`Footprint` counts, and the update's two branches are the model of the write's
destructive and copying cases. A proof module has no pre-fix behaviour to
observe, so the checks here meet its definitions and theorems from outside, on
heaps a client of the module can build. They are of six kinds:

* **The counts themselves**, as `#guard`s of evaluated results on small heaps: the
  count of an exclusively owned cell, the count of a cell a second handle names,
  a count an allocation begins with, a count an increment raises and a count a
  release lowers. Each detector has an affirmative control beside it — a false
  equation of the same `#guard` shape whose message is pinned — so a guard is
  shown to fire rather than to pass whatever it is given.
* **The update's two branches**, as `#guard`s of the location the updated slots
  are read back at: at a count of one the write keeps the location, and at a count
  of two the updated slots land at a fresh one while the old cell keeps its own.
* **Negative controls** as theorems about specific heaps: the cell the second
  handle names is not exclusive, and an update below the take-out pair's carried
  cell does not keep its location. Each stands beside an affirmative control at
  the *same* heap — the exclusive cell of the same heap, and the fresh location
  the same update's slots land at — so the negative is about the reference and not
  about the heap being rejected everywhere.
* **Affirmative structural controls**: the heaps are counted by way of
  `counted_of`, the three operations' preservation theorems build a heap that is
  `Counted` from one that is, and `counted_iff_exclusive`,
  `update_preserves_location_of_exclusive` and `update_copies_of_shared` are
  applied at those heaps.
* **The take-out pair**, at the counted heap: the pair's carried cell is not
  exclusive, and dropping the pair's handle makes it exclusive again.
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
The runtime's release returns the count to one: the increment's two is lowered by
the one handle the release takes out.
-/
#guard decide (CHeap.count (drop (dup chain [0] 0).1 [0, 0] 0).1 0 = 1)
#guard decide ((drop (dup chain [0] 0).1 [0, 0] 0).2 = [0])

/--
error: Expression
  decide ((drop (dup chain [0] 0).fst [0, 0] 0).fst.count 0 = 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (CHeap.count (drop (dup chain [0] 0).1 [0, 0] 0).1 0 = 2)

/-
The exclusive cell's update keeps its location: the write's slots are read back at
the same reference, and the leaf the old slots named loses that occurrence, which
is why its count falls to zero.
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
at the *same* heap, so the negative is about the reference and not about the heap.
The take-out pair is then read at the counted heap: the carried cell is not
exclusive, dropping the pair's handle makes it exclusive, and the update below it
copies until the drop. -/

/-- The cell the second handle names is not exclusive: the slot occurrence and the
second handle are two live references.

Its affirmative counterpart is `chain_root_exclusive` at the root of a heap of the
same shape, whose one handle is one live reference. -/
theorem shared_not_exclusive : ¬ Exclusive (CHeap.presentation shared) [0, 1] 1 := by
  intro h
  have h1 : CHeap.count shared 1 = 1 := (counted_iff_exclusive shared_counted 1).mpr h
  rw [show CHeap.count shared 1 = 2 from by decide] at h1
  omega

/-- An update below the aliased cell does not keep its location: the slots the
write hands it are not read back at the cell the second handle names, because the
write landed at the fresh location instead.

Its affirmative counterpart is `shared_update_copies`, which reads the same slots
back at that fresh location at the same heap. -/
theorem shared_update_not_at_leaf : (update shared [0, 1] 1 [0]).1.lookup 1 ≠ some [0] := by
  decide

/-- The updated slots of the same write, read at the fresh location: the copy is
where the write landed, which is the affirmative control beside
`shared_update_not_at_leaf`. -/
theorem shared_update_at_fresh : (update shared [0, 1] 1 [0]).1.lookup 2 = some [0] := by
  decide

/-- The take-out pair's carried cell is not exclusive: the pair's two handles are
two live references, whatever the heap names.

Its affirmative counterpart is `pair_dropped_exclusive`, the same heap after the
pair's handle is dropped. -/
theorem pair_not_exclusive : ¬ Exclusive (CHeap.presentation pairHeap) [0, 0] 0 :=
  (takeout_pair_count_two pair_counted (by decide)).2

/-- The pair's count is two, read at the heap's own field: the value a write tests
below the element is the count the pair's second handle raised. -/
theorem pair_count_two : CHeap.count pairHeap 0 = 2 :=
  (takeout_pair_count_two pair_counted (by decide)).1

/-- Dropping the pair's handle makes the carried cell exclusive again. -/
theorem pair_dropped_exclusive :
    Exclusive (CHeap.presentation (drop pairHeap [0, 0] 0).1) (drop pairHeap [0, 0] 0).2 0 :=
  (takeout_dropped_count_one pair_counted (by decide)).2

/-- The pair at the update's decision: with the pair's handle held the update below
the element copies, and with the handle dropped first the same update keeps the
location. -/
theorem pair_update_branches :
    (update pairHeap [0, 0] 0 []).1.lookup (fresh pairHeap []) = some [] ∧
      (update (drop pairHeap [0, 0] 0).1 (drop pairHeap [0, 0] 0).2 0 []).1.lookup 0 = some [] :=
  takeout_pair_update_branches pair_counted (by decide) (by decide)

/-
The pair's two states as evaluated results, each with its own control.
-/
#guard decide ((update pairHeap [0, 0] 0 []).1.lookup (fresh pairHeap []) = some [])
#guard decide ((update (drop pairHeap [0, 0] 0).1 (drop pairHeap [0, 0] 0).2 0 []).1.lookup 0
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
  decide ((update (drop pairHeap [0, 0] 0).fst (drop pairHeap [0, 0] 0).snd 0 []).fst.lookup 0 = some [1])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((update (drop pairHeap [0, 0] 0).1 (drop pairHeap [0, 0] 0).2 0 []).1.lookup 0
  = some [1])

/-! ## The operations' preservation, and the bridge, at these heaps

Each theorem is exercised at a concrete heap: the counts above are met by a heap
the module's own operations built from a counted one, so the preservation theorems
are applied and not only read. -/

/-- The leaf an allocation of the root extends: one cell named by no slot. -/
theorem allocLeaf_counted : Counted (alloc leafHeap [1] 0 []).1 (alloc leafHeap [1] 0 []).2 :=
  counted_alloc leafHeap_counted (r := 0) (ks := []) (by decide) (by decide)
    (by intro x hx; simp at hx)

/-- The increment's heap is counted: the handle it adds and the count it raises
name the same reference. -/
theorem dup_counted : Counted (dup chain [0] 0).1 (dup chain [0] 0).2 :=
  counted_dup chain_counted (r := 0) (by decide)

/-- The release's heap is counted at the handle list it returns. -/
theorem drop_counted :
    Counted (drop (dup chain [0] 0).1 [0, 0] 0).1 (drop (dup chain [0] 0).1 [0, 0] 0).2 :=
  counted_drop dup_counted (r := 0) (by decide)

/-- The bridge at the chain's root, read from the heap's own count: a count of one
and `Footprint`'s exclusivity are the same statement there. -/
theorem chain_count_iff_exclusive :
    CHeap.count chain 0 = 1 ↔ Exclusive (CHeap.presentation chain) [0] 0 :=
  counted_iff_exclusive chain_counted 0

/-- The chain's root is exclusive under the one handle that names it. -/
theorem chain_root_exclusive : Exclusive (CHeap.presentation chain) [0] 0 :=
  (chain_count_iff_exclusive).mp (by decide)

/-- The destructive branch at the chain's root: the write keeps the location. -/
theorem chain_update_keeps_location : (update chain [0] 0 []).1.lookup 0 = some [] :=
  update_preserves_location_of_exclusive chain_counted chain_root_exclusive

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
  counted_update_exclusive chain_counted chain_root_exclusive (by decide) (by decide)
    (by intro x hx; simp at hx)

/-- The copying branch preserves `Counted`. -/
theorem shared_update_counted : Counted (update shared [0, 1] 1 []).1 (update shared [0, 1] 1 []).2 :=
  counted_update_copy shared_counted shared_not_exclusive (r := 1) (ks := [])
    (by decide) (by decide) (by intro x hx; simp at hx)

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
info: 'Scidonia.FracPerm.StateVar.RCHeap.counted_drop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_drop

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
