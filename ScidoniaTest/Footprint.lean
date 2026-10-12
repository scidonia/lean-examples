/-
Compile-time checks for `Scidonia.FracPerm.StateVar.Footprint`.

The module is a counted presentation of the heap: what the count of a reference
*is*, defined from aliasing, and the facts behind the model's classification of a
cell as out-of-place exactly when its count is not one. It has no pre-fix
behaviour to observe
— it is a proof module — so the checks here meet its definitions and theorems
from outside, on presentations a client of the module can build. They are of six
kinds:

* **The counts themselves**, as `#guard`s of evaluated results on small
  presentations: a chain of cells read from a root handle, a store whose two
  slots name one cell, a store plus a second handle, a store that names no cell,
  and a write that cuts one cell's slots. Each detector has an affirmative
  control beside it — a false equation of the same `#guard` shape whose message
  is pinned — so a guard is shown to fire rather than to pass whatever it is
  given.
* **The issued-value layer**, as `#guard`s of the references a `Value` names and
  of the handles a list of issued read results holds, each with its own pinned
  control, and as the bridge `noRef_iff_refs_count` read at a location that
  differs and at the root itself — the second carried by
  `not_noRef_loc_self`, so the bridge's two sides are both exercised.
* **The composition**, as the composition theorem applied at a concrete
  presentation and value list, beside its countermodel at the same handle-list
  shape and an affirmative counterpart that differs from the countermodel only in
  the issued value: the count of one is bought with detachment, and the count of
  two is what an issued result naming the root gives instead.
* **Negative controls** as theorems about aliased presentations: the store whose
  two slots name one cell is not exclusive with no handle, and the chain with a
  second handle on an interior cell is not exclusive. Each stands beside an
  affirmative control on the *same* presentation — the root that is exclusive —
  so the negative control is about the reference and not merely about the
  presentation.
* **Affirmative structural controls**: the single-handle, take-out-pair and
  one-cell-write theorems applied at those presentations, and the two statements
  of `pair_needs_the_drop` read off one call.
* **The runtime link**, used as what it is: `RuntimeAgrees` stays a hypothesis,
  never constructed here or in the module under check, and the theorems below take
  it as an argument — the model's count at an exclusive state reaches the
  runtime's test through it. Its other direction has no non-vacuous concrete
  instance, so its statement is pinned by the output of `#check` rather than
  exercised. The axiom lists are then asserted: each representative theorem's
  `#print axioms` output is pinned to the standard kernel principles, so a proof
  that acquires any other axiom fails the build rather than printing a longer
  list for a reader to notice.
-/
import Scidonia.FracPerm.StateVar.Footprint

open Scidonia.FracPerm.StateVar
open Scidonia.FracPerm.StateVar.Footprint

namespace ScidoniaTest.Footprint

/-! ## The presentations the counts are read at

Four small presentations, written so that the cell a write changes can be named
on its own: the chain is its two parts with the interior cell between them. -/

/-- The cell above the chain's interior cell: the root, whose one slot names the
interior cell. -/
def chainAbove : Presentation := [(0, Node.cell [1])]

/-- The cell below the chain's interior cell: an observation leaf. -/
def chainBelow : Presentation := [(2, Node.leaf .unit ())]

/-- The chain's interior cell: its one slot names the leaf. -/
def chainInterior : Node := Node.cell [2]

/-- A chain of three cells: the root names the interior cell, which names the
leaf. Every node in it is named by exactly one slot. -/
def chainHeap : Presentation := chainAbove ++ (1, chainInterior) :: chainBelow

/-- A store whose root has two slots naming the same cell: the two-parent store
the write discipline's aliasing case is about. -/
def twoParentHeap : Presentation := [(0, Node.cell [1, 1]), (1, Node.cell [])]

/-- A store that names no cell: one observation leaf under no slot, so the
presentation has no occurrence at all. -/
def leafHeap : Presentation := [(0, Node.leaf .nat 7)]

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
#guard decide ((Presentation.setSlots chainHeap 1 []).occurrences 2 = 0)

/--
error: Expression
  decide ((chainHeap.setSlots 1 []).occurrences 2 = 1)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide ((Presentation.setSlots chainHeap 1 []).occurrences 2 = 1)

#guard decide ((Presentation.setSlots chainHeap 1 []).occurrences 1 = 1)

/--
error: Expression
  decide ((chainHeap.setSlots 1 []).occurrences 1 = 2)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide ((Presentation.setSlots chainHeap 1 []).occurrences 1 = 2)

#guard decide (refCount (Presentation.setSlots chainHeap 1 []) [2] 2 = 1)

/--
error: Expression
  decide (refCount (chainHeap.setSlots 1 []) [2] 2 = 2)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (refCount (Presentation.setSlots chainHeap 1 []) [2] 2 = 2)

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
    (Presentation.setSlots chainHeap 1 []).occurrences 2 = 0 :=
  (Presentation.setSlots_occurrences chainAbove chainBelow chainInterior 1 [] 2
    (by decide) (by decide)).trans (by decide)

/-- The single-handle count after the write: with its slot cut, the leaf is named
by nothing but the one handle, so the model's single-handle theorem applies to
the written presentation — the drop the discipline theorem asks for, at a
presentation the write produced. -/
theorem chain_cut_then_single_handle :
    refCount (Presentation.setSlots chainHeap 1 []) [2] 2 = 1 :=
  refCount_single_handle (Presentation.setSlots chainHeap 1 []) 2 chain_cut_detaches_leaf

/-! ## The references an issued value names

The values a read hands out are the layer the interface quantifies over, and this
module's counts are a layer about the references such a value names. `Value.refs`
is the list a value's references are counted in, and `noRef_iff_refs_count` is the
bridge from the interface's `NoRef` to that list's count being zero. Every guard
below has an affirmative control beside it — a false equation of the same shape
whose message is pinned — so the guard is shown to fire. -/

/-
A value's references, in order: a location names itself, a pair names both
components in order, and a leaf names none — a `.nat` payload is immutable data
and contributes no handle.
-/
#guard decide (Value.refs (.loc 3) = [3])
#guard decide (Value.refs (.pair (.loc 1) (.loc 2)) = [1, 2])
#guard decide (Value.refs (.nat 7) = ([] : List Ref))

/--
error: Expression
  decide (Value.refs (Value.loc 3) = [4])
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (Value.refs (.loc 3) = [4])

/--
error: Expression
  decide (Value.refs ((Value.loc 1).pair (Value.loc 2)) = [2, 1])
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (Value.refs (.pair (.loc 1) (.loc 2)) = [2, 1])

/--
error: Expression
  decide (Value.refs (Value.nat 7) = [7])
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (Value.refs (.nat 7) = [7])

/-
The handles a list of issued values holds, end to end: two issued results naming
different roots hold both references, in order.
-/
#guard decide (handlesOf [Value.loc 1, Value.loc 2] = [1, 2])

/--
error: Expression
  decide (handlesOf [Value.loc 1, Value.loc 2] = [2, 1])
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (handlesOf [Value.loc 1, Value.loc 2] = [2, 1])

/-
The bridge at a location that differs and at the root itself: the count of a root
among the value's references is zero exactly when the value is detached from it.
-/
#guard decide ((Value.refs (.loc 3)).count 5 = 0)
#guard decide ((Value.refs (.loc 3)).count 3 = 1)

/--
error: Expression
  decide (List.count 5 (Value.refs (Value.loc 3)) = 1)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide ((Value.refs (.loc 3)).count 5 = 1)

/--
error: Expression
  decide (List.count 3 (Value.refs (Value.loc 3)) = 0)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide ((Value.refs (.loc 3)).count 3 = 0)

/-- The bridge at a location that differs: the value names no root at `5`, so the
count of `5` among the references it names is zero. -/
theorem refs_bridge_other_count : (Value.refs (.loc 3)).count 5 = 0 :=
  (noRef_iff_refs_count 5 (.loc 3)).mp (noRef_loc_of_ne (by decide))

/-- The bridge at the root itself: the value names the root, so the count of it
among the references it names is not zero.

Its affirmative counterpart is `refs_bridge_other_count` — the same value and the
same bridge, read at a location the value does not name — so this is about the
root the value names and not about the value. -/
theorem refs_bridge_self_count : (Value.refs (.loc 3)).count 3 ≠ 0 :=
  fun h => not_noRef_loc_self 3 ((noRef_iff_refs_count 3 (.loc 3)).mpr h)

/-! ## The composition at a concrete presentation

The root's count at a run's issued read results, at the chain: the presentation
reading and the issued-values reading, together. The countermodel and its
affirmative counterpart share the presentation and the handle-list shape and
differ only in the issued value, so what the count turns on is the value. -/

/-- The issued read results of the run below: a natural, which names no root, and
a location at another root. Both are detached from root `0`. -/
theorem run_issues_detached :
    ∀ v ∈ [Value.nat 3, Value.loc 2], NoRef 0 v := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact noRef_nat 0 3
  · exact noRef_loc_of_ne (by decide)

/-- The composition at the chain: the run's issued read results are detached from
the root, no slot of the presentation names it, and the root's count is one. -/
theorem detached_run_count_one :
    refCount chainHeap (0 :: handlesOf [Value.nat 3, Value.loc 2]) 0 = 1 :=
  refCount_one_of_detached_issues chainHeap [Value.nat 3, Value.loc 2] 0 (by decide)
    run_issues_detached

/-- The affirmative counterpart of the countermodel below, at the same
presentation and the same handle-list shape: the issued read result names another
root rather than the root itself, and the root's count is one.

The two theorems differ only in the issued value, so the countermodel is about
detachment and not about the presentation or the runner's own handle. -/
theorem issued_other_count_one :
    refCount chainHeap (0 :: handlesOf [Value.loc 2]) 0 = 1 :=
  refCount_one_of_detached_issues chainHeap [Value.loc 2] 0 (by decide)
    (by
      intro v hv
      rw [List.mem_singleton] at hv
      rcases hv with rfl
      exact noRef_loc_of_ne (by decide))

/-- The countermodel at the same shape: the issued read result names the root
itself, so the handle list is `[0, 0]` and the root's count is two — an encoding
that puts a `.loc` where the interface's detachment forbids one, or a raw handle,
is not exclusive, and detachment is what the count of one was bought with. -/
theorem issued_loc_self_not_exclusive :
    refCount chainHeap (0 :: handlesOf [Value.loc 0]) 0 = 2 ∧
      ¬ Exclusive chainHeap (0 :: handlesOf [Value.loc 0]) 0 :=
  not_exclusive_of_issued_loc chainHeap 0 (by decide)

/-
The two counts as evaluated results, each with its own control.
-/
#guard decide (refCount chainHeap (0 :: handlesOf [Value.nat 3, Value.loc 2]) 0 = 1)
#guard decide (refCount chainHeap (0 :: handlesOf [Value.loc 0]) 0 = 2)

/--
error: Expression
  decide (refCount chainHeap (0 :: handlesOf [Value.nat 3, Value.loc 2]) 0 = 2)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (refCount chainHeap (0 :: handlesOf [Value.nat 3, Value.loc 2]) 0 = 2)

/--
error: Expression
  decide (refCount chainHeap (0 :: handlesOf [Value.loc 0]) 0 = 1)
did not evaluate to `true`
-/
#guard_msgs in
#guard decide (refCount chainHeap (0 :: handlesOf [Value.loc 0]) 0 = 1)

/-! ## The runtime link, used as a hypothesis

`RuntimeAgrees` is the link from this model to the runtime's own test and is not
proved anywhere: no instance of it is constructed in this module or in the library
module it checks. The forward direction is used at a presentation whose
exclusivity holds — the model's count at that state reaches
`RefCount.IsExclusive` through the link, which arrives as a hypothesis of
`chain_runtime_exclusive`. The reverse direction has no non-vacuous concrete
instance and is pinned as the statement it is rather than exercised. The runtime
predicate's own values at one and at two stand beside them, as the values any such
link is read at. -/

/-- The runtime's exclusive count itself: one reference, single-threaded. It is
the runtime predicate's own value at one, which is where the conclusion of
`runtime_agrees_exclusive` is stated; any link from the model to it is the
`RuntimeAgrees` hypothesis of that theorem, not this value. -/
theorem runtime_count_one_exclusive : Scidonia.FracPerm.StateVar.RefCount.IsExclusive (1 : Int32) := by
  simp only [Scidonia.FracPerm.StateVar.RefCount.IsExclusive,
    Scidonia.FracPerm.StateVar.RefCount.isSt, decide_eq_true_eq]
  grind

/-- The count of two as the runtime reads and tests it: its own `refCount` reads
the count as two, and the count is not exclusive. It is the runtime predicate's
own value at two; whether a model pair of handles corresponds to it is what a
`RuntimeAgrees` hypothesis would state, not something this value shows. -/
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

/-- The model's count reaching the runtime's test through the link, at the
chain's root: the model says exclusive, and the link — an argument of this
theorem, not an instance constructed anywhere — carries that to
`RefCount.IsExclusive` at whatever counter it describes. -/
theorem chain_runtime_exclusive (rc : Int32) (hag : RuntimeAgrees chainHeap [0] 0 rc) :
    Scidonia.FracPerm.StateVar.RefCount.IsExclusive rc :=
  runtime_agrees_exclusive chainHeap [0] 0 rc chain_root_exclusive hag

/-
The link in the other direction, pinned as a statement rather than exercised: a
runtime count that fails the runtime's test carries back to non-exclusivity at the
model layer while the link holds.

No presentation can exercise it non-vacuously. At a fixed presentation the
`RuntimeAgrees` hypothesis is satisfiable only when the conclusion already holds:
the hypothesis is the implication from `Exclusive` to the runtime's predicate, so
an exclusive state forces the runtime's test to pass and refutes the premise that
it fails, while a state that is not exclusive is what the conclusion states and
the hypothesis has nothing to say about it. What the theorem constrains is the
signature — the link's two directions read against each other at every state at
once — and that is what the check below pins.

A bare `#check` would not exercise that constraint: it reports that the name
elaborates and prints whatever statement the name currently has, so a theorem of
a different statement under the same name would still build. The message the
command emits is therefore pinned instead. `#guard_msgs` compares the whole of
it, so what is required is this statement and no other: the binders in order,
each with the name it is written under and its type, the `RuntimeAgrees`
hypothesis and the failed runtime test between them, and the conclusion at the
model layer. An argument reordered, dropped or retyped under the same name, a
binder renamed, or a name that no longer resolves, fails the build.

The statement pinned is the one the theorem is stated with, and the comparison
is loose in whitespace only, so the line breaks the printer happens to choose
are not part of it. Binder names are part of it, so a rename of a hypothesis —
which leaves the statement itself unchanged — fails the build too; the price of
reading the statement off the emitted message rather than restating it.
-/
/--
info: Scidonia.FracPerm.StateVar.Footprint.runtime_not_exclusive_excludes_model (h : Presentation) (handles : List Ref)
  (r : Ref) (rc : Int32) (hag : RuntimeAgrees h handles r rc) (hrc : ¬RefCount.IsExclusive rc) : ¬Exclusive h handles r
-/
#guard_msgs (whitespace := lax) in
#check Scidonia.FracPerm.StateVar.Footprint.runtime_not_exclusive_excludes_model

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
model's lists and nothing more. The issued-value layer's lists are the same two
principles, for the same reason, with one exception: `handlesOf_append` is
`propext` alone, since its proof is a `simp` through `List.flatMap_append` and
never touches a `List.count`. The bridge `noRef_iff_refs_count` and the
composition are `propext` and `Quot.sound`, and
`readAt_result_holds_no_handle` inherits exactly the bridge's list: the
interface's detachment enters as a hypothesis and brings no axiom with it. The
runtime link's own theorem rests on nothing, being an application of the
hypothesis it was handed. The one list that carries all three standard principles
is the runtime count's: `Classical.choice` comes from the `grind` proof of the
runtime's own predicate over `Int32`, which is the one place in this module where
the counter vocabulary is touched. No list carries anything outside the standard
set. -/

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
info: 'Scidonia.FracPerm.StateVar.Footprint.Presentation.setSlots_occurrences' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Presentation.setSlots_occurrences

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

/--
info: 'Scidonia.FracPerm.StateVar.Footprint.noRef_iff_refs_count' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms noRef_iff_refs_count

/--
info: 'Scidonia.FracPerm.StateVar.Footprint.handlesOf_append' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms handlesOf_append

/--
info: 'Scidonia.FracPerm.StateVar.Footprint.handlesOf_count_eq_zero_of_detached' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms handlesOf_count_eq_zero_of_detached

/--
info: 'Scidonia.FracPerm.StateVar.Footprint.refCount_one_of_detached_issues' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refCount_one_of_detached_issues

/--
info: 'Scidonia.FracPerm.StateVar.Footprint.not_exclusive_of_issued_loc' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_exclusive_of_issued_loc

/--
info: 'Scidonia.FracPerm.StateVar.Footprint.readAt_result_holds_no_handle' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms readAt_result_holds_no_handle

/--
info: 'ScidoniaTest.Footprint.detached_run_count_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms detached_run_count_one

/--
info: 'ScidoniaTest.Footprint.issued_loc_self_not_exclusive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms issued_loc_self_not_exclusive

end ScidoniaTest.Footprint
