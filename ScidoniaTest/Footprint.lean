/-
Compile-time checks for `Scidonia.FracPerm.StateVar.Footprint`.

The module is a counted presentation of the heap: what the count of a reference
*is*, defined from aliasing, and the facts that make the out-of-place cases
exactly the cells whose count is not one. It has no pre-fix behaviour to observe
— it is a proof module — so the checks here meet its definitions and theorems
from outside, on presentations a client of the module can build. They are of four
kinds:

* **The counts themselves**, as `#guard`s of evaluated results on small
  presentations: a chain of cells read from a root handle, a store whose two
  slots name one cell, a store plus a second handle, a store that names no cell,
  and a write that cuts one cell's slots. Each detector has an affirmative
  control beside it — a false equation of the same `#guard` shape whose message
  is pinned — so a guard is shown to fire rather than to pass whatever it is
  given.
* **Negative controls** as theorems about aliased presentations: the store whose
  two slots name one cell is not exclusive with no handle, and the chain with a
  second handle on an interior cell is not exclusive. Each stands beside an
  affirmative control on the *same* presentation — the root that is exclusive —
  so the negative control is about the reference and not merely about the
  presentation.
* **Affirmative structural controls**: the single-handle, take-out-pair and
  one-cell-write theorems applied at those presentations, and the two statements
  of `pair_needs_the_drop` read off one call.
* **The runtime link**, used as what it is: `RuntimeAgrees` is inhabited at a
  state the model calls exclusive, the model's count reaches the runtime's test
  through it, and a runtime count that fails the test carries back to the model's
  side. The axiom lists are then asserted: each representative theorem's
  `#print axioms` output is pinned to the standard kernel principles, so a proof
  that acquires any other axiom fails the build rather than printing a longer
  list for a reader to notice.
-/
import Scidonia.FracPerm.StateVar.Footprint

open Scidonia.FracPerm.StateVar.Footprint

namespace ScidoniaTest.Footprint

/-! ## The presentations the counts are read at

Four small presentations, written so that the cell a write changes can be named
on its own: the chain is its two parts with the interior cell between them. -/

/-- The cell above the chain's interior cell: the root, whose one slot names the
interior cell. -/
def chainAbove : Heap := [(0, Node.cell [1])]

/-- The cell below the chain's interior cell: an observation leaf. -/
def chainBelow : Heap := [(2, Node.leaf .unit ())]

/-- The chain's interior cell: its one slot names the leaf. -/
def chainInterior : Node := Node.cell [2]

/-- A chain of three cells: the root names the interior cell, which names the
leaf. Every node in it is named by exactly one slot. -/
def chainHeap : Heap := chainAbove ++ (1, chainInterior) :: chainBelow

/-- A store whose root has two slots naming the same cell: the two-parent store
the write discipline's aliasing case is about. -/
def twoParentHeap : Heap := [(0, Node.cell [1, 1]), (1, Node.cell [])]

/-- A store that names no cell: one observation leaf under no slot, so the
presentation has no occurrence at all. -/
def leafHeap : Heap := [(0, Node.leaf .nat 7)]

/-! ## The counts, evaluated

Every `#guard` below is answered by an affirmative control: a false equation of
the same shape whose reported message is pinned, so the guard is shown to fire and
not to pass whatever it is given. The three chain counts share one control, since
they are the same equation at three references and one reported failure shows that
shape fires; each other guard has its own. A doc comment cannot stand immediately
before a `#guard` (the parser rejects it), so the guards carry plain block
comments and only the controls carry the pinned message. -/

/-
The chain read from the root's handle: the root is named by no slot and by the
one handle, so its count is one; the interior cell is named by the root's slot
and by no handle, so its count is one as well; so is the leaf's.
-/
#guard decide (refCount chainHeap [0] 0 = 1)
#guard decide (refCount chainHeap [0] 1 = 1)
#guard decide (refCount chainHeap [0] 2 = 1)

/--
error: Expression
  decide (refCount chainHeap [0] 0 = 2)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (refCount chainHeap [0] 0 = 2)

/-
The store whose two slots name one cell: the aliased cell has count two with no
handle at all, and the root, which no slot names, has count one.
-/
#guard decide (refCount twoParentHeap [] 1 = 2)

/--
error: Expression
  decide (refCount twoParentHeap [] 1 = 1)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (refCount twoParentHeap [] 1 = 1)

#guard decide (refCount twoParentHeap [0] 0 = 1)

/--
error: Expression
  decide (refCount twoParentHeap [0] 0 = 2)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (refCount twoParentHeap [0] 0 = 2)

/-
The chain with a second handle on the interior cell: the slot that names the cell
and the extra handle are two names, so the count is two.
-/
#guard decide (refCount chainHeap [0, 1] 1 = 2)

/--
error: Expression
  decide (refCount chainHeap [0, 1] 1 = 1)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (refCount chainHeap [0, 1] 1 = 1)

/-
The take-out pair on the root's own reference: two handles to a cell no slot
names are two live references. The pair's handle list is what
`pair_needs_the_drop` drops.
-/
#guard decide (refCount chainHeap [0, 0] 0 = 2)

/--
error: Expression
  decide (refCount chainHeap [0, 0] 0 = 1)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (refCount chainHeap [0, 0] 0 = 1)

/-
The store that names no cell has no occurrence: the leaf's count under no handle
is zero, not one.
-/
#guard decide (refCount leafHeap [] 0 = 0)

/--
error: Expression
  decide (refCount leafHeap [] 0 = 1)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (refCount leafHeap [] 0 = 1)

/-
One cell's slots cut to the empty list: the interior cell no longer names the
leaf, so the leaf's occurrences drop to none and its count under one handle is
one. The cell the root names is still named once — the write is on the interior
cell alone.
-/
#guard decide ((Heap.setSlots chainHeap 1 []).occurrences 2 = 0)

/--
error: Expression
  decide ((chainHeap.setSlots 1 []).occurrences 2 = 1)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide ((Heap.setSlots chainHeap 1 []).occurrences 2 = 1)

#guard decide ((Heap.setSlots chainHeap 1 []).occurrences 1 = 1)

/--
error: Expression
  decide ((chainHeap.setSlots 1 []).occurrences 1 = 2)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide ((Heap.setSlots chainHeap 1 []).occurrences 1 = 2)

#guard decide (refCount (Heap.setSlots chainHeap 1 []) [2] 2 = 1)

/--
error: Expression
  decide (refCount (chainHeap.setSlots 1 []) [2] 2 = 2)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (refCount (Heap.setSlots chainHeap 1 []) [2] 2 = 2)

/-! ## Negative controls, and their affirmative counterparts

The specific presentations whose obligation is false: the store whose two slots
name one cell, and the chain with a second handle on an interior cell. Beside
each stands a presentation that *is* exclusive at the reference it holds, so the
negative control is about aliasing and not about the presentation being rejected
for every reference. -/

/-- The store whose root's two slots name the same cell is not exclusive there:
two slot occurrences alone are two live references, whatever handles are held.

Its affirmative counterpart is `twoParent_root_exclusive`: the *root* of the same
presentation, which no slot names, is exclusive under one handle. -/
theorem twoParent_not_exclusive : ¬ Exclusive twoParentHeap [] 1 :=
  not_exclusive_of_two_occurrences (by decide)

/-- The root of the two-parent store is exclusive under one handle: the same
presentation that refuses exclusivity at the aliased cell grants it at the cell
the handle names. This is the control that keeps `twoParent_not_exclusive` from
being a statement about the presentation alone. -/
theorem twoParent_root_exclusive : Exclusive twoParentHeap [0] 0 :=
  exclusive_single_handle twoParentHeap 0 (by decide)

/-- The chain with a second handle on the interior cell is not exclusive there:
the slot that names the cell and the extra handle are two live references.

Its affirmative counterpart is `chain_root_exclusive`: the root of the same chain
under one handle is exclusive. -/
theorem chain_second_handle_not_exclusive : ¬ Exclusive chainHeap [0, 1] 1 :=
  not_exclusive_of_slot_and_handle (by decide) (by decide)

/-- The chain's root is exclusive under one handle: it is named by no slot, so
one handle is one live reference. -/
theorem chain_root_exclusive : Exclusive chainHeap [0] 0 :=
  exclusive_single_handle chainHeap 0 (by decide)

/-! ## The model's theorems at these presentations

The single-handle, take-out-pair and one-cell-write facts, applied at the
presentations above, so that each theorem is exercised at a concrete heap and not
only read. -/

/-- The single-handle count at the chain's root, from the model's own theorem. -/
theorem chain_root_count_one : refCount chainHeap [0] 0 = 1 :=
  refCount_single_handle chainHeap 0 (by decide)

/-- The take-out pair at the chain's root: two handles to a reference no slot
names are two live references. -/
theorem chain_root_pair_two : refCount chainHeap [0, 0] 0 = 2 :=
  refCount_pair_of_no_slot chainHeap 0 (by decide)

/-- The pair at the chain's root is not exclusive without any hypothesis on the
presentation: the two handles alone carry the count past one, whatever the store
names. -/
theorem chain_root_pair_not_exclusive : ¬ Exclusive chainHeap [0, 0] 0 :=
  not_exclusive_pair chainHeap 0

/-- The two sides of the discipline theorem at one call: the pair's count is two
and the single handle's count is one, at the same presentation. It is the pair's
extra reference that a write below the element must not hold. -/
theorem chain_discipline :
    refCount chainHeap [0, 0] 0 = 2 ∧ refCount chainHeap [0] 0 = 1 :=
  pair_needs_the_drop chainHeap 0 (by decide)

/-- One cell's write, read at the counts the presentation has afterwards: cutting
the interior cell's slots to the empty list takes the leaf's occurrences to none,
which is the changed cell's new contribution (nothing) plus every other cell's
(the root still names the interior cell, and nothing names the leaf).

The two parts are the split the theorem is stated over: `chainAbove` above the
written cell and `chainBelow` below it, with the written cell named between
them. -/
theorem chain_cut_detaches_leaf :
    (Heap.setSlots chainHeap 1 []).occurrences 2 = 0 :=
  (Heap.setSlots_occurrences chainAbove chainBelow chainInterior 1 [] 2
    (by decide) (by decide)).trans (by decide)

/-- The single-handle count after the write: with its slot cut, the leaf is named
by nothing but the one handle, so the model's single-handle theorem applies to
the written presentation — the drop the discipline theorem asks for, at a
presentation the write produced. -/
theorem chain_cut_then_single_handle :
    refCount (Heap.setSlots chainHeap 1 []) [2] 2 = 1 :=
  refCount_single_handle (Heap.setSlots chainHeap 1 []) 2 chain_cut_detaches_leaf

/-! ## The runtime link, used as a hypothesis

`RuntimeAgrees` is the link from this model to the runtime's own test and is not
proved anywhere. The checks below use it where it is the hypothesis: inhabited at
a state the model calls exclusive, so the model's count reaches
`RefCount.IsExclusive`; and, at the pair, a runtime count that fails the test
carries back to the model's side. -/

/-- The runtime's exclusive count itself: one reference, single-threaded. This is
the affirmative control for the conclusion of `runtime_agrees_exclusive` — without
it, the link could not be inhabited at any state. -/
theorem runtime_count_one_exclusive : Scidonia.FracPerm.StateVar.RefCount.IsExclusive (1 : Int32) := by
  simp only [Scidonia.FracPerm.StateVar.RefCount.IsExclusive,
    Scidonia.FracPerm.StateVar.RefCount.isSt, decide_eq_true_eq]
  grind

/-- The count of two as the runtime reads and tests it: its own `refCount` reads
the count as two, and the count is not exclusive. It is the count a pair of live
references stands for. -/
theorem runtime_count_two :
    Scidonia.FracPerm.StateVar.RefCount.refCount (2 : Int32) = 2 ∧
      ¬ Scidonia.FracPerm.StateVar.RefCount.IsExclusive (2 : Int32) := by
  constructor
  · simp only [Scidonia.FracPerm.StateVar.RefCount.refCount,
      Scidonia.FracPerm.StateVar.RefCount.isSt, decide_eq_true_eq]
    decide
  · simp only [Scidonia.FracPerm.StateVar.RefCount.IsExclusive,
      Scidonia.FracPerm.StateVar.RefCount.isSt, decide_eq_true_eq]
    grind

/-- The link inhabited at a state the model calls exclusive: at the chain's root
under one handle, a runtime count of one satisfies "exclusive model state implies
the runtime's test passes". This is the link as a hypothesis — it is fed in, not
derived — and it says nothing about what a compiled object's count would be. -/
theorem chain_runtime_link : RuntimeAgrees chainHeap [0] 0 (1 : Int32) :=
  fun _ => runtime_count_one_exclusive

/-- The model's count reaching the runtime's test through the link, at the
chain's root: the model says exclusive, the link says that means
`RefCount.IsExclusive`, and the runtime's predicate holds of the count of one. -/
theorem chain_runtime_exclusive : Scidonia.FracPerm.StateVar.RefCount.IsExclusive (1 : Int32) :=
  runtime_agrees_exclusive chainHeap [0] 0 1 chain_root_exclusive chain_runtime_link

/-- The link in the other direction, at the pair: a runtime count of two fails the
runtime's test, so a state the runtime count describes as not exclusive cannot be
exclusive in the model either.

The `RuntimeAgrees` instance here has a false premise — the aliased store is not
exclusive, as `twoParent_not_exclusive` says — which is why it is inhabited; it is
still the link the theorem takes as a hypothesis, and no part of this proves that
a compiled object's count is the modelled one. -/
theorem twoParent_runtime_excludes_exclusive : ¬ Exclusive twoParentHeap [] 1 :=
  runtime_not_exclusive_excludes_model twoParentHeap [] 1 2
    (fun hx => absurd hx twoParent_not_exclusive) runtime_count_two.2

/-! ## Axioms of representative theorems

The facts above are proved with `simp`, `omega`, `grind`, `rw` and `decide`, which
are kernel-checked and add no axiom, so each must rest on standard kernel
principles and no others. These are asserted rather than printed: each
`#guard_msgs` pins the message `#print axioms` emits, so a proof that acquires any
axiom fails the build instead of printing a longer list for a reader to notice.
Whitespace is compared loosely, so what is pinned is the names, not the line
breaks they happen to wrap at.

The lists are the whole of what each theorem rests on, not a hope. The model's
theorems that count, that prove the pair's count and that write one cell's slots
rest on `propext` and `Quot.sound` — `omega`'s arithmetic and the `List` lemmas —
and the check module's own applications at the concrete presentations rest on the
model's lists and nothing more. The runtime link's own theorem rests on nothing,
being an application of the hypothesis it was handed. The one list that carries
all three standard principles is the runtime count's: `Classical.choice` comes
from the `grind` proof of the runtime's own predicate over `Int32`, which is the
one place in this module where the counter vocabulary is touched. No list carries
anything outside the standard set. -/

/--
info: 'Scidonia.FracPerm.StateVar.Footprint.not_exclusive_of_two_occurrences' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_exclusive_of_two_occurrences

/--
info: 'Scidonia.FracPerm.StateVar.Footprint.refCount_pair_of_no_slot' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refCount_pair_of_no_slot

/--
info: 'Scidonia.FracPerm.StateVar.Footprint.Heap.setSlots_occurrences' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Heap.setSlots_occurrences

/--
info: 'Scidonia.FracPerm.StateVar.Footprint.pair_needs_the_drop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pair_needs_the_drop

/--
info: 'Scidonia.FracPerm.StateVar.Footprint.runtime_agrees_exclusive' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms runtime_agrees_exclusive

/--
info: 'ScidoniaTest.Footprint.chain_discipline' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chain_discipline

/--
info: 'ScidoniaTest.Footprint.chain_cut_detaches_leaf' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chain_cut_detaches_leaf

/--
info: 'ScidoniaTest.Footprint.runtime_count_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms runtime_count_two

end ScidoniaTest.Footprint
