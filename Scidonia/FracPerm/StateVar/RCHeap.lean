/-
A counted heap: a location and a reference count as state.

`Scidonia.FracPerm.StateVar.Footprint` defines the count of a reference from
aliasing alone. A presentation lists the live cells and the references their
slots hold, and the count of a reference is its slot occurrences among them plus
the handles held outside the store. That makes the count a *function* of the
referencing structure, but not state: nothing in a presentation says what the
runtime keeps for a cell, and nothing in it can be written to.

This module makes the pair state. A cell of the counted heap carries its slots
and a count, and the heap is the list of live cells. `Counted` is the invariant
that ties the two together: every cell's count is what `Footprint` counts for it
— its slot occurrences among the live cells, plus the outside handles that name
it. A count of one is therefore a fact about the referencing structure, and not a
number someone maintained by hand.

## What is proved

* the bridge `counted_iff_exclusive`: under `Counted`, a cell's count being one
  and `Footprint.Exclusive` at it are the same statement.
* the three operations the runtime performs on a count — `alloc`, a fresh cell
  with its slot list, count one and the new handle handed out; `dup`, the
  runtime's increment, a second handle naming the reference and the count up by
  one; `drop`, the runtime's drop, a handle released and the count down by one —
  each preserve `Counted`, from a `Counted` input and under the operation's own
  premise.
* the update in its two branches, as the model of the lowering's
  `isExclusiveUnsafe` / `lean_array_uset` decision: when the cell's count is one
  the write is destructive and the cell keeps its location, and otherwise the
  updated slots land at a fresh location while the old cell keeps its slots and
  loses a reference (`update_preserves_location_of_exclusive`,
  `update_copies_of_shared`). `Counted` survives both branches.
* the take-out pair at the counted heap: the pair's second handle on the
  extracted element makes its count two, so an update below it copies, and
  dropping that handle first restores the count of one, so the update keeps the
  location (`takeout_pair_count_two`, `takeout_dropped_count_one`,
  `takeout_pair_update_branches`).

## What is modelled

A location here is a `Ref`: a name in a list, not a machine address. Two heaps
never share one, and nothing here says where a cell lives. The location a copied
cell takes is a model location, chosen beyond every reference the heap and the
new slots mention; it is a name, not an allocator's answer.

The count is the runtime's count *modelled*: a `Nat` that `Counted` ties to
aliasing, not the machine word an object carries. `RefCount` is the counter-level
vocabulary of the runtime's own test, and no instance of a correspondence between
a count here and the `Int32` an object carries is built in this module.

The two branches of `update` are the model of the lowering's
`isExclusiveUnsafe` / `lean_array_uset` decision, and the model's decision is the
heap's own count being one. The counts an operation moves are moved together
with the occurrences they count: `writeSlots` takes the written
cell's old slots out of the counts of the cells those slots named and puts `ks`
in, and `addOccurrences` adds the occurrences a new cell's slots contribute. Each
operation also carries the premises that make it well defined at the heap it is
applied to — a fresh cell's reference is not already listed, a slot names a live
cell, a drop releases a handle the handle list holds, the written cell does not
name itself — and each of those is a statement about this model heap.

## What is trusted, and what is outside

Two links to a compiled run are trusted rather than built here:

* that Lean's compiler lowers the write paths of this repository — the structured
  interface's `set`, and a leaf write such as the slot's `setLeaf` — into a term
  of the shape modelled here: a test of the object's count, a destructive update
  on the one branch and a fresh object on the other.
* that the array-write decision itself lives in the runtime's `lean_array_uset`
  and `lean_ensure_exclusive_array`, and not in the emitted IR. The IR carries a
  call to the array's write; the branch that decides whether it mutates or copies
  is inside the code the compiler emits for that call, so the branch this module
  models is not a branch of the IR and cannot be read off it.

No theorem here says anything about a compiled program: not that a compiled write
updates in place, not that a copy happens when it does not, and nothing about
Lean's object graph, its allocation, or the compiler's reset/reuse pass. The
counts are logical counts of occurrences, the locations are names, and the
run-time evidence for the copy-or-mutate behaviour of a compiled write stays where
it was, in the in-place check of `FracPerm`.

This module imports `Scidonia.FracPerm.StateVar.Footprint`, builds on its `Ref`,
`Node`, `Presentation`, `refCount` and `Exclusive`, and changes none of them. It
adds no runtime code: nothing in it runs.
-/
import Scidonia.FracPerm.StateVar.Footprint

namespace Scidonia.FracPerm.StateVar
namespace RCHeap

open Scidonia.FracPerm.StateVar.Footprint

/-! ## The counted heap

A cell carries the references its slots hold and the count the runtime keeps for
it; the heap is the list of live cells. The projections below read the structure
back: the presentation a count is defined against, the heap's own slot
occurrences, its live references, and the slot list and count of the first cell
it lists at a reference. -/

/-- A cell of the counted heap: the references its slots hold, and the count the
runtime keeps for it. -/
structure Cell where
  /-- The references this cell's slots hold, in order, repetitions included. -/
  slots : List Ref
  /-- The count the runtime keeps for this cell. -/
  count : Nat
deriving DecidableEq, Repr

/-- A counted heap: the live cells, each with its cell.

The list is read as exactly the live cells, as a `Footprint` presentation is: a
heap that listed a cell twice or left a live cell out would still satisfy every
theorem below. -/
abbrev CHeap := List (Ref × Cell)

/-- The cell a fresh allocation or a copy begins with: the new slots, and count
one. -/
def cellOf (ks : List Ref) : Cell := { slots := ks, count := 1 }

/-- A fresh cell holds the slots it was given. -/
@[simp] theorem cellOf_slots (ks : List Ref) : (cellOf ks).slots = ks := rfl

/-- A fresh cell's count is one. -/
@[simp] theorem cellOf_count (ks : List Ref) : (cellOf ks).count = 1 := rfl

/-- The live cells as a `Footprint` presentation: the counts are dropped and each
cell becomes the node carrying its slots. -/
def CHeap.presentation (c : CHeap) : Presentation :=
  c.map (fun e => (e.1, Node.cell e.2.slots))

/-- Every reference occurrence in the heap's slots, in cell order: the heap's own
side of the count. -/
def CHeap.slots (c : CHeap) : List Ref := c.flatMap (fun e => e.2.slots)

/-- The references the heap lists, in cell order. -/
def CHeap.refs (c : CHeap) : List Ref := c.map (fun e => e.1)

/-- The slots of the first cell the heap lists at `r`, or `none` when it lists no
cell there. -/
def CHeap.lookup : CHeap → Ref → Option (List Ref)
  | [], _ => none
  | (r', cl) :: t, r => if r' = r then some cl.slots else CHeap.lookup t r

/-- The slots of the first cell the heap lists at `r`, or the empty list when it
lists no cell there. -/
def CHeap.slotsAt (c : CHeap) (r : Ref) : List Ref := (CHeap.lookup c r).getD []

/-- The count the heap keeps for `r`: the count of the first cell it lists at `r`,
or zero when it lists no cell there. -/
def CHeap.count : CHeap → Ref → Nat
  | [], _ => 0
  | (r', cl) :: t, r => if r' = r then cl.count else CHeap.count t r

/-! ## Reading the heap

The elementary equations the definitions above reduce by, and the first facts
about a cell the heap does not list. -/

/-- An empty heap lists no reference. -/
@[simp] theorem CHeap.refs_nil : CHeap.refs ([] : CHeap) = [] := rfl

/-- A heap prepends the head's reference to the live references. -/
@[simp] theorem CHeap.refs_cons (r : Ref) (cl : Cell) (t : CHeap) :
    CHeap.refs ((r, cl) :: t) = r :: CHeap.refs t := rfl

/-- An empty heap contributes no occurrence. -/
@[simp] theorem CHeap.slots_nil : CHeap.slots ([] : CHeap) = ([] : List Ref) := rfl

/-- A heap prepends the head's slots to the rest of the occurrences. -/
@[simp] theorem CHeap.slots_cons (r : Ref) (cl : Cell) (t : CHeap) :
    CHeap.slots ((r, cl) :: t) = cl.slots ++ CHeap.slots t := by
  simp [CHeap.slots]

/-- An empty heap lists no cell. -/
@[simp] theorem CHeap.lookup_nil (r : Ref) : CHeap.lookup ([] : CHeap) r = none := rfl

/-- The heap's first cell at the head's own reference is the head. -/
@[simp] theorem CHeap.lookup_cons_self (r : Ref) (cl : Cell) (t : CHeap) :
    CHeap.lookup ((r, cl) :: t) r = some cl.slots := by
  simp [CHeap.lookup]

/-- A head at another reference leaves the lookup to the tail. -/
@[simp] theorem CHeap.lookup_cons_of_ne {r' : Ref} (h : r' ≠ r) (cl : Cell) (t : CHeap) :
    CHeap.lookup ((r', cl) :: t) r = CHeap.lookup t r := by
  simp [CHeap.lookup, h]

/-- An empty heap keeps no count. -/
@[simp] theorem CHeap.count_nil (r : Ref) : CHeap.count ([] : CHeap) r = 0 := rfl

/-- The heap's count at the head's own reference is the head's count. -/
@[simp] theorem CHeap.count_cons_self (r : Ref) (cl : Cell) (t : CHeap) :
    CHeap.count ((r, cl) :: t) r = cl.count := by
  simp [CHeap.count]

/-- A head at another reference leaves the count to the tail. -/
@[simp] theorem CHeap.count_cons_of_ne {r' : Ref} (h : r' ≠ r) (cl : Cell) (t : CHeap) :
    CHeap.count ((r', cl) :: t) r = CHeap.count t r := by
  simp [CHeap.count, h]

/-- The first cell at the head's own reference has the head's slots. -/
@[simp] theorem CHeap.slotsAt_cons_self (r : Ref) (cl : Cell) (t : CHeap) :
    CHeap.slotsAt ((r, cl) :: t) r = cl.slots := by
  simp [CHeap.slotsAt, CHeap.lookup]

/-- A head at another reference leaves the slots to the tail. -/
@[simp] theorem CHeap.slotsAt_cons_of_ne {r' : Ref} (h : r' ≠ r) (cl : Cell) (t : CHeap) :
    CHeap.slotsAt ((r', cl) :: t) r = CHeap.slotsAt t r := by
  simp [CHeap.slotsAt, CHeap.lookup, h]

/-- A reference the head does not carry is one the tail carries. -/
theorem CHeap.mem_refs_cons_of_ne {r' : Ref} {cl : Cell} {t : CHeap} {r : Ref}
    (h : r ∈ CHeap.refs ((r', cl) :: t)) (hne : r ≠ r') : r ∈ CHeap.refs t := by
  rw [CHeap.refs_cons] at h
  exact (List.mem_cons.mp h).resolve_left hne

/-- A heap that lists no cell at `r` keeps a count of zero there. -/
theorem CHeap.count_eq_zero_of_not_mem {c : CHeap} {x : Ref} (h : x ∉ CHeap.refs c) :
    CHeap.count c x = 0 := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      have h' : x ≠ r' := fun hh => h (by rw [CHeap.refs_cons, hh]; exact List.mem_cons_self ..)
      have ht : x ∉ CHeap.refs t :=
        fun hmem => h (by rw [CHeap.refs_cons]; exact List.mem_cons_of_mem r' hmem)
      rw [CHeap.count_cons_of_ne (by exact fun hh => h' hh.symm) cl t, ih ht]

/-- A cell with a positive count is a cell the heap lists. -/
theorem CHeap.mem_refs_of_count_pos (c : CHeap) {x : Ref} (h : 0 < CHeap.count c x) :
    x ∈ CHeap.refs c := by
  induction c with
  | nil => simp [CHeap.count] at h
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases hx : r' = x
      · rw [CHeap.refs_cons, hx]
        exact List.mem_cons_self ..
      · rw [CHeap.count_cons_of_ne hx cl t] at h
        rw [CHeap.refs_cons]
        exact List.mem_cons_of_mem r' (ih h)

/-! ## The bridge: the heap's slots are the presentation's occurrences

`Footprint` counts a reference among the occurrences its presentation lists; the
heap lists the same occurrences in `CHeap.slots`. The two counts are the same, so
every fact below can be read at the heap's own slot list. -/

/-- The presentation's occurrences are the heap's own slot occurrences. -/
theorem CHeap.presentation_slots (c : CHeap) : (CHeap.presentation c).slots = CHeap.slots c := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r, cl⟩ := e
      show Presentation.slots ((r, Node.cell cl.slots) :: CHeap.presentation t)
        = CHeap.slots ((r, cl) :: t)
      rw [Presentation.slots_cons, Node.slots_cell, ih, CHeap.slots_cons]

/-- The count `Footprint` reads from the heap's presentation is the count of the
heap's own slot occurrences. -/
theorem CHeap.occurrences_presentation (c : CHeap) (r : Ref) :
    (CHeap.presentation c).occurrences r = (CHeap.slots c).count r := by
  rw [Presentation.occurrences, CHeap.presentation_slots]

/-! ## The invariant

`Counted` is the one statement this module is built on, and `counted_iff_slots`
is its arithmetic form: each cell's count is its occurrences among the live cells
plus its occurrences among the outside handles. -/

/-- The counts are the aliasing counts: every cell's count is what `Footprint`
counts for it — its slot occurrences among the live cells plus the outside
handles that name it. This is the bridge that makes a count of one a fact about
the referencing structure rather than a field someone maintained by hand.

A reference the heap does not list has count zero here, so `Counted` also says
that no handle names a cell the heap leaves out and no slot names one: the heap
and its handle list name only live cells. -/
def Counted (c : CHeap) (handles : List Ref) : Prop :=
  ∀ r, CHeap.count c r = refCount (CHeap.presentation c) handles r

/-- `Counted` in the heap's own arithmetic: every reference's count is its
occurrences among the heap's slots plus its occurrences among the handles. -/
theorem counted_iff_slots (c : CHeap) (handles : List Ref) :
    Counted c handles ↔
      ∀ r, CHeap.count c r = (CHeap.slots c).count r + handles.count r := by
  constructor
  · intro h r
    rw [h r]
    simp [refCount, CHeap.occurrences_presentation]
  · intro h r
    rw [h r]
    simp [refCount, CHeap.occurrences_presentation]

/-- Under `Counted`, a cell's count being one is `Footprint`'s exclusivity at it:
the two tests a write makes are the same statement. -/
theorem counted_iff_exclusive {c : CHeap} {handles : List Ref} (h : Counted c handles) (r : Ref) :
    CHeap.count c r = 1 ↔ Exclusive (CHeap.presentation c) handles r := by
  have hr : CHeap.count c r = refCount (CHeap.presentation c) handles r := h r
  exact iff_of_eq (congrArg (· = 1) hr)

/-- A reference the heap does not list occurs in no slot: under `Counted`, a slot
names a live cell. -/
theorem Counted.slots_count_eq_zero {c : CHeap} {handles : List Ref} (hc : Counted c handles)
    {x : Ref} (h : x ∉ CHeap.refs c) : (CHeap.slots c).count x = 0 := by
  have hc' : CHeap.count c x = (CHeap.slots c).count x + handles.count x :=
    (counted_iff_slots c handles).mp hc x
  rw [CHeap.count_eq_zero_of_not_mem h] at hc'
  omega

/-- A reference the heap does not list is named by no handle either: under
`Counted`, a handle names a live cell. -/
theorem Counted.handles_count_eq_zero {c : CHeap} {handles : List Ref} (hc : Counted c handles)
    {x : Ref} (h : x ∉ CHeap.refs c) : handles.count x = 0 := by
  have hc' : CHeap.count c x = (CHeap.slots c).count x + handles.count x :=
    (counted_iff_slots c handles).mp hc x
  rw [CHeap.count_eq_zero_of_not_mem h] at hc'
  omega

/-- The reference occurrences one live cell's slots contribute are at most the
heap's: the cell's slots are part of the heap's slot list. -/
theorem CHeap.slotsAt_count_le_slots (c : CHeap) (r : Ref) (hr : r ∈ CHeap.refs c) (y : Ref) :
    (CHeap.slotsAt c r).count y ≤ (CHeap.slots c).count y := by
  induction c with
  | nil => simp [CHeap.refs] at hr
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · rw [← h, CHeap.slotsAt_cons_self, CHeap.slots_cons, List.count_append]
        omega
      · have hr' : r ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne hr (by exact fun hh => h hh.symm)
        rw [CHeap.slotsAt_cons_of_ne h, CHeap.slots_cons, List.count_append]
        have := ih hr'
        omega

/-! ## The runtime's increment and drop

`adjust` is the one step both share: the first cell the heap lists at a reference
has its count replaced by the function of its old count. -/

/-- The heap with the first cell it lists at `r` given the count `f` returns for
its old count, and every other cell left as it is. -/
def CHeap.adjust : CHeap → Ref → (Nat → Nat) → CHeap
  | [], _, _ => []
  | (r', cl) :: t, r, f =>
      if r' = r then (r', { cl with count := f cl.count }) :: t else (r', cl) :: CHeap.adjust t r f

/-- An empty heap has nothing to adjust. -/
@[simp] theorem CHeap.adjust_nil (r : Ref) (f : Nat → Nat) :
    CHeap.adjust ([] : CHeap) r f = [] := rfl

/-- The head is adjusted when its reference is the one asked for. -/
@[simp] theorem CHeap.adjust_cons_self (r : Ref) (cl : Cell) (t : CHeap) (f : Nat → Nat) :
    CHeap.adjust ((r, cl) :: t) r f = (r, { cl with count := f cl.count }) :: t := by
  simp [CHeap.adjust]

/-- A head at another reference is kept and the tail is adjusted. -/
@[simp] theorem CHeap.adjust_cons_of_ne {r' : Ref} (h : r' ≠ r) (cl : Cell) (t : CHeap)
    (f : Nat → Nat) :
    CHeap.adjust ((r', cl) :: t) r f = (r', cl) :: CHeap.adjust t r f := by
  simp [CHeap.adjust, h]

/-- Adjusting a count changes no slots. -/
theorem CHeap.slots_adjust (c : CHeap) (r : Ref) (f : Nat → Nat) :
    CHeap.slots (CHeap.adjust c r f) = CHeap.slots c := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · rw [← h, CHeap.adjust_cons_self, CHeap.slots_cons, CHeap.slots_cons]
      · rw [CHeap.adjust_cons_of_ne h, CHeap.slots_cons, CHeap.slots_cons, ih]

/-- Adjusting a count lists the same references. -/
theorem CHeap.refs_adjust (c : CHeap) (r : Ref) (f : Nat → Nat) :
    CHeap.refs (CHeap.adjust c r f) = CHeap.refs c := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · rw [← h, CHeap.adjust_cons_self, CHeap.refs_cons, CHeap.refs_cons]
      · rw [CHeap.adjust_cons_of_ne h, CHeap.refs_cons, CHeap.refs_cons, ih]

/-- Adjusting a count reads the same slots at every reference: the slots and their
order are untouched. -/
theorem CHeap.lookup_adjust (c : CHeap) (r : Ref) (f : Nat → Nat) (x : Ref) :
    CHeap.lookup (CHeap.adjust c r f) x = CHeap.lookup c x := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · by_cases hx : r' = x
        · rw [← h, ← hx, CHeap.adjust_cons_self, CHeap.lookup_cons_self,
            CHeap.lookup_cons_self]
        · rw [← h, CHeap.adjust_cons_self, CHeap.lookup_cons_of_ne hx,
            CHeap.lookup_cons_of_ne hx]
      · by_cases hx : r' = x
        · rw [← hx, CHeap.adjust_cons_of_ne h, CHeap.lookup_cons_self, CHeap.lookup_cons_self]
        · rw [CHeap.adjust_cons_of_ne h, CHeap.lookup_cons_of_ne hx,
            CHeap.lookup_cons_of_ne hx, ih]

/-- The adjusted cell's count is the function's value at its old count. -/
theorem CHeap.count_adjust_self (c : CHeap) (r : Ref) (f : Nat → Nat)
    (hr : r ∈ CHeap.refs c) : CHeap.count (CHeap.adjust c r f) r = f (CHeap.count c r) := by
  induction c with
  | nil => simp [CHeap.refs] at hr
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · rw [← h, CHeap.adjust_cons_self, CHeap.count_cons_self, CHeap.count_cons_self]
      · have hr' : r ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne hr (by exact fun hh => h hh.symm)
        rw [CHeap.adjust_cons_of_ne h, CHeap.count_cons_of_ne h, CHeap.count_cons_of_ne h]
        exact ih hr'

/-- Another reference's count is untouched by the adjustment. -/
theorem CHeap.count_adjust_of_ne (c : CHeap) (r : Ref) (f : Nat → Nat) {x : Ref} (hx : x ≠ r) :
    CHeap.count (CHeap.adjust c r f) x = CHeap.count c x := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · have hrx : r' ≠ x := fun hh => hx (hh.symm.trans h)
        rw [← h, CHeap.adjust_cons_self, CHeap.count_cons_of_ne hrx, CHeap.count_cons_of_ne hrx]
      · by_cases hxr : r' = x
        · rw [← hxr, CHeap.adjust_cons_of_ne h, CHeap.count_cons_self, CHeap.count_cons_self]
        · rw [CHeap.adjust_cons_of_ne h, CHeap.count_cons_of_ne hxr, CHeap.count_cons_of_ne hxr]
          exact ih

/-- A cell's count moved by the change in the occurrences that name it: a cell
whose reference is `y` loses the occurrences the written cell's old slots `old`
contributed at `y` and gains those `ks` contributes. -/
def shiftCount (old ks : List Ref) (y : Ref) (cl : Cell) : Cell :=
  { cl with count := cl.count - old.count y + ks.count y }

/-- A moved cell's count: its old count, less the occurrences the written cell's
old slots contributed at its reference, plus those `ks` contributes. -/
theorem shiftCount_count (old ks : List Ref) (y : Ref) (cl : Cell) :
    (shiftCount old ks y cl).count = cl.count - old.count y + ks.count y := by
  simp [shiftCount]

/-- The moving cell itself, with its reference kept. -/
def shiftCell (old ks : List Ref) (e : Ref × Cell) : Ref × Cell :=
  (e.1, shiftCount old ks e.1 e.2)

/-- A moved cell, written out as the pair its reference and moved cell are. -/
theorem shiftCell_pair (old ks : List Ref) (r : Ref) (cl : Cell) :
    shiftCell old ks (r, cl) = (r, shiftCount old ks r cl) := rfl

/-- A moved cell holds the same slots. -/
@[simp] theorem shiftCount_slots (old ks : List Ref) (y : Ref) (cl : Cell) :
    (shiftCount old ks y cl).slots = cl.slots := rfl

/-- A moved cell holds the same slots. -/
@[simp] theorem shiftCell_slots (old ks : List Ref) (e : Ref × Cell) :
    (shiftCell old ks e).2.slots = e.2.slots := rfl

/-! ## The destructive write

`writeSlots` is the write the lowering performs when the count is one: the first
cell the heap lists at `r` gets the slots `ks` and keeps its location, and every
other cell's count moves by the change in the occurrences that name it — a cell
the written cell's old slots named loses those occurrences, and a cell `ks` names
gains them. -/

/-- The heap with the first cell it lists at `r` given the slots `ks`, and every
other cell's count moved by the change in the occurrences that name it.

A cell before the written one in the list reads the old slots at `r` from the tail
it is followed by; the cells after the written one read them from the written cell
itself. Either way exactly one cell's slots change, and every other cell's count
moves by the same amount as the occurrences that name it. -/
def CHeap.writeSlotsAux (ks : List Ref) (r : Ref) : CHeap → CHeap
  | [] => []
  | (r', cl) :: t =>
      if r' = r then (r', { cl with slots := ks }) :: t.map (shiftCell cl.slots ks)
      else shiftCell (CHeap.slotsAt t r) ks (r', cl) :: CHeap.writeSlotsAux ks r t

/-- The heap with the slots of the first cell it lists at `r` replaced by `ks`,
and every other cell's count moved by the change in the occurrences that name it.
A heap that lists no cell at `r` is returned with no slots changed and its counts
moved by the occurrences `ks` contributes, since no cell's slots hold them. -/
def CHeap.writeSlots (c : CHeap) (r : Ref) (ks : List Ref) : CHeap :=
  CHeap.writeSlotsAux ks r c

/-- The write is the auxiliary recursion on the heap itself. -/
theorem CHeap.writeSlots_eq (c : CHeap) (r : Ref) (ks : List Ref) :
    CHeap.writeSlots c r ks = CHeap.writeSlotsAux ks r c := rfl

/-- An empty heap has nothing to write. -/
@[simp] theorem CHeap.writeSlotsAux_nil (ks : List Ref) (r : Ref) :
    CHeap.writeSlotsAux ks r ([] : CHeap) = [] := rfl

/-- At the written cell's own reference the write fires: the head gets the slots
and the tail's counts move. -/
@[simp] theorem CHeap.writeSlotsAux_cons_self (ks : List Ref) (r : Ref) (cl : Cell) (t : CHeap) :
    CHeap.writeSlotsAux ks r ((r, cl) :: t)
      = (r, { cl with slots := ks }) :: t.map (shiftCell cl.slots ks) := by
  simp [CHeap.writeSlotsAux]

/-- At another reference the head's count moves and the tail is written. -/
@[simp] theorem CHeap.writeSlotsAux_cons_of_ne {r' : Ref} (h : r' ≠ r) (ks : List Ref) (cl : Cell)
    (t : CHeap) :
    CHeap.writeSlotsAux ks r ((r', cl) :: t)
      = shiftCell (CHeap.slotsAt t r) ks (r', cl) :: CHeap.writeSlotsAux ks r t := by
  simp [CHeap.writeSlotsAux, h]

/-- Moving a whole heap's cells changes none of its slots. -/
theorem CHeap.slots_map_shiftCell (c : CHeap) (old ks : List Ref) :
    CHeap.slots (c.map (shiftCell old ks)) = CHeap.slots c := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      rw [List.map_cons, shiftCell_pair, CHeap.slots_cons, CHeap.slots_cons, shiftCount_slots, ih]

/-- Moving a whole heap's cells keeps a reference's count at its moved value. -/
theorem CHeap.count_map_shiftCell_mem (c : CHeap) (old ks : List Ref) {x : Ref}
    (hx : x ∈ CHeap.refs c) :
    CHeap.count (c.map (shiftCell old ks)) x
      = CHeap.count c x - old.count x + ks.count x := by
  induction c with
  | nil => simp [CHeap.refs] at hx
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = x
      · rw [← h, List.map_cons, shiftCell_pair, CHeap.count_cons_self, CHeap.count_cons_self]
        rw [shiftCount_count]
      · have hx' : x ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne hx (by exact fun hh => h hh.symm)
        rw [List.map_cons, shiftCell_pair, CHeap.count_cons_of_ne h, CHeap.count_cons_of_ne h,
          ih hx']

/-- A heap that lists no cell at a reference moves no count there. -/
theorem CHeap.count_map_shiftCell_not_mem (c : CHeap) (old ks : List Ref) {x : Ref}
    (hx : x ∉ CHeap.refs c) : CHeap.count (c.map (shiftCell old ks)) x = 0 := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      have h' : x ≠ r' := fun hh => hx (by simp [CHeap.refs_cons, hh])
      have ht : x ∉ CHeap.refs t := fun hmem => hx (by simp [CHeap.refs_cons, hmem])
      rw [List.map_cons, shiftCell_pair, CHeap.count_cons_of_ne (by exact fun hh => h' hh.symm),
        ih ht]

/-- The written cell's slots are `ks` at its own location. -/
theorem CHeap.lookup_writeSlots_self (c : CHeap) (r : Ref) (ks : List Ref)
    (hr : r ∈ CHeap.refs c) : CHeap.lookup (CHeap.writeSlots c r ks) r = some ks := by
  induction c with
  | nil => simp [CHeap.refs] at hr
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · rw [← h, CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_self, CHeap.lookup_cons_self]
      · have hr' : r ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne hr (by exact fun hh => h hh.symm)
        rw [CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_of_ne h, shiftCell_pair,
          CHeap.lookup_cons_of_ne (by exact h)]
        exact ih hr'

/-- The written cell's count is untouched: what its own slots contribute is
unchanged, and so are the handles. -/
theorem CHeap.count_writeSlots_self (c : CHeap) (r : Ref) (ks : List Ref)
    (hr : r ∈ CHeap.refs c) : CHeap.count (CHeap.writeSlots c r ks) r = CHeap.count c r := by
  induction c with
  | nil => simp [CHeap.refs] at hr
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · rw [← h, CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_self, CHeap.count_cons_self,
          CHeap.count_cons_self]
      · have hr' : r ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne hr (by exact fun hh => h hh.symm)
        rw [CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_of_ne h, shiftCell_pair,
          CHeap.count_cons_of_ne (by exact h), CHeap.count_cons_of_ne (by exact h)]
        exact ih hr'

/-- Another live cell's count moves by exactly the change in the occurrences that
name it. -/
theorem CHeap.count_writeSlots_of_ne (c : CHeap) (r : Ref) (ks : List Ref) {x : Ref}
    (hx : x ≠ r) (hx' : x ∈ CHeap.refs c) (hr : r ∈ CHeap.refs c) :
    CHeap.count (CHeap.writeSlots c r ks) x
      = CHeap.count c x - (CHeap.slotsAt c r).count x + ks.count x := by
  induction c with
  | nil => simp [CHeap.refs] at hx'
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · have hx'' : x ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne hx' (fun hh => hx (hh.trans h))
        have hrx : r' ≠ x := fun hh => hx (hh.symm.trans h)
        rw [← h, CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_self, CHeap.slotsAt_cons_self,
          CHeap.count_cons_of_ne hrx, CHeap.count_cons_of_ne hrx]
        rw [CHeap.count_map_shiftCell_mem t cl.slots ks hx'']
      · have hr' : r ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne hr (by exact fun hh => h hh.symm)
        by_cases hxr : r' = x
        · rw [← hxr, CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_of_ne h, shiftCell_pair,
            CHeap.slotsAt_cons_of_ne h, CHeap.count_cons_self, CHeap.count_cons_self]
          rw [shiftCount_count]
        · have hx'' : x ∈ CHeap.refs t :=
            CHeap.mem_refs_cons_of_ne hx' (by exact fun hh => hxr hh.symm)
          rw [CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_of_ne h, shiftCell_pair,
            CHeap.slotsAt_cons_of_ne h, CHeap.count_cons_of_ne hxr, CHeap.count_cons_of_ne hxr]
          exact ih hx'' hr'

/-- A cell the heap does not list is neither moved nor read: the write leaves its
count at zero. -/
theorem CHeap.count_writeSlots_not_mem (c : CHeap) (r : Ref) (ks : List Ref) {x : Ref}
    (hx : x ∉ CHeap.refs c) : CHeap.count (CHeap.writeSlots c r ks) x = 0 := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      have h' : x ≠ r' := fun hh => hx (by simp [CHeap.refs_cons, hh])
      have ht : x ∉ CHeap.refs t := fun hmem => hx (by simp [CHeap.refs_cons, hmem])
      by_cases h : r' = r
      · rw [← h, CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_self,
          CHeap.count_cons_of_ne (by exact fun hh => h' hh.symm)]
        rw [CHeap.count_map_shiftCell_not_mem t cl.slots ks ht]
      · rw [CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_of_ne h, shiftCell_pair,
          CHeap.count_cons_of_ne (by exact fun hh => h' hh.symm)]
        exact ih ht

/-- The write's effect on the occurrence counts: the heap's occurrences at a
reference lose what the written cell's old slots contributed and gain what `ks`
contributes. -/
theorem CHeap.count_slots_writeSlots (c : CHeap) (r : Ref) (ks : List Ref)
    (hr : r ∈ CHeap.refs c) (y : Ref) :
    (CHeap.slots (CHeap.writeSlots c r ks)).count y
      = (CHeap.slots c).count y - (CHeap.slotsAt c r).count y + ks.count y := by
  induction c with
  | nil => simp [CHeap.refs] at hr
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · rw [← h, CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_self, CHeap.slotsAt_cons_self]
        simp only [CHeap.slots_cons, CHeap.slots_map_shiftCell, List.count_append]
        omega
      · have hr' : r ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne hr (by exact fun hh => h hh.symm)
        have hbound := CHeap.slotsAt_count_le_slots t r hr' y
        have hih := ih hr'
        rw [CHeap.writeSlots_eq] at hih
        rw [CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_of_ne h, shiftCell_pair,
          CHeap.slotsAt_cons_of_ne h]
        simp only [CHeap.slots_cons, shiftCount_slots, List.count_append]
        omega

/-! ## The fresh location

A copied cell takes a model location beyond every reference the heap and the new
slots mention, so it is a location the heap did not list and `ks` does not name. -/

/-- The largest reference in a list, or zero when the list is empty. -/
def listTop : List Ref → Ref
  | [] => 0
  | x :: t => max x (listTop t)

/-- [`listTop`] bounds every member of its list. -/
theorem le_listTop_of_mem {l : List Ref} {x : Ref} (h : x ∈ l) : x ≤ listTop l := by
  induction l with
  | nil => simp at h
  | cons y t ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- The model location a copied cell takes: beyond every reference the heap lists
and beyond every reference `ks` names. -/
def fresh (c : CHeap) (ks : List Ref) : Ref :=
  max (listTop (CHeap.refs c)) (listTop ks) + 1

/-- The fresh location is not one the heap lists. -/
theorem fresh_not_mem_refs (c : CHeap) (ks : List Ref) : fresh c ks ∉ CHeap.refs c := by
  intro h
  have h1 : fresh c ks ≤ listTop (CHeap.refs c) := le_listTop_of_mem h
  have h2 : listTop (CHeap.refs c) + 1 ≤ fresh c ks := by
    rw [fresh]
    exact Nat.add_le_add_right (Nat.le_max_left _ _) 1
  exact absurd (Nat.le_trans h2 h1) (Nat.not_le.mpr (Nat.lt_succ_self _))

/-- The fresh location is not one `ks` names. -/
theorem fresh_not_mem_ks (c : CHeap) (ks : List Ref) : fresh c ks ∉ ks := by
  intro h
  have h1 : fresh c ks ≤ listTop ks := le_listTop_of_mem h
  have h2 : listTop ks + 1 ≤ fresh c ks := by
    rw [fresh]
    exact Nat.add_le_add_right (Nat.le_max_right _ _) 1
  exact absurd (Nat.le_trans h2 h1) (Nat.not_le.mpr (Nat.lt_succ_self _))

/-- A fresh location is not a reference the heap lists. -/
theorem fresh_ne_of_mem_refs {c : CHeap} {ks : List Ref} {r : Ref} (hr : r ∈ CHeap.refs c) :
    fresh c ks ≠ r :=
  fun h => fresh_not_mem_refs c ks (h ▸ hr)

/-! ## Occurrences a new cell's slots add

`addOccurrences` raises each live cell's count by the number of times a new slot
list names it: the references a fresh cell holds. -/

/-- The heap with each live cell's count raised by the number of times `ks` names
it. -/
def CHeap.addOccurrences : CHeap → List Ref → CHeap
  | [], _ => []
  | (r, cl) :: t, ks => (r, { cl with count := cl.count + ks.count r }) :: CHeap.addOccurrences t ks

/-- Raising the counts prepends the head's raised count to the rest. -/
theorem CHeap.addOccurrences_cons (r : Ref) (cl : Cell) (t : CHeap) (ks : List Ref) :
    CHeap.addOccurrences ((r, cl) :: t) ks
      = (r, { cl with count := cl.count + ks.count r }) :: CHeap.addOccurrences t ks := rfl

/-- Raising the counts changes no slots. -/
theorem CHeap.slots_addOccurrences (c : CHeap) (ks : List Ref) :
    CHeap.slots (CHeap.addOccurrences c ks) = CHeap.slots c := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r, cl⟩ := e
      rw [CHeap.addOccurrences_cons, CHeap.slots_cons, CHeap.slots_cons, ih]

/-- Raising the counts lists the same references. -/
theorem CHeap.refs_addOccurrences (c : CHeap) (ks : List Ref) :
    CHeap.refs (CHeap.addOccurrences c ks) = CHeap.refs c := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r, cl⟩ := e
      rw [CHeap.addOccurrences_cons, CHeap.refs_cons, CHeap.refs_cons, ih]

/-- Raising the counts reads the same slots at every reference. -/
theorem CHeap.lookup_addOccurrences (c : CHeap) (ks : List Ref) (x : Ref) :
    CHeap.lookup (CHeap.addOccurrences c ks) x = CHeap.lookup c x := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r, cl⟩ := e
      by_cases hx : r = x
      · rw [CHeap.addOccurrences_cons, ← hx, CHeap.lookup_cons_self, CHeap.lookup_cons_self]
      · rw [CHeap.addOccurrences_cons, CHeap.lookup_cons_of_ne hx, CHeap.lookup_cons_of_ne hx,
          ih]

/-- A live cell's count is raised by the occurrences `ks` contributes at it. -/
theorem CHeap.count_addOccurrences_mem (c : CHeap) (ks : List Ref) {x : Ref}
    (hx : x ∈ CHeap.refs c) :
    CHeap.count (CHeap.addOccurrences c ks) x = CHeap.count c x + ks.count x := by
  induction c with
  | nil => simp [CHeap.refs] at hx
  | cons e t ih =>
      obtain ⟨r, cl⟩ := e
      by_cases h : r = x
      · rw [CHeap.addOccurrences_cons, ← h, CHeap.count_cons_self, CHeap.count_cons_self]
      · have hx' : x ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne hx (by exact fun hh => h hh.symm)
        rw [CHeap.addOccurrences_cons, CHeap.count_cons_of_ne h, CHeap.count_cons_of_ne h,
          ih hx']

/-- A cell the heap does not list is not raised: the heap lists no cell there. -/
theorem CHeap.count_addOccurrences_not_mem (c : CHeap) (ks : List Ref) {x : Ref}
    (hx : x ∉ CHeap.refs c) : CHeap.count (CHeap.addOccurrences c ks) x = 0 := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r, cl⟩ := e
      have h' : x ≠ r := fun hh => hx (by simp [CHeap.refs_cons, hh])
      have ht : x ∉ CHeap.refs t := fun hmem => hx (by simp [CHeap.refs_cons, hmem])
      rw [CHeap.addOccurrences_cons, CHeap.count_cons_of_ne (by exact fun hh => h' hh.symm),
        ih ht]

/-! ## The handle list

`dropHandle` releases one occurrence of a reference from the handles held outside
the store. -/

/-- The handle list with the first occurrence of `r` released, and the rest kept.
A list that does not hold `r` is returned unchanged. -/
def dropHandle : List Ref → Ref → List Ref
  | [], _ => []
  | x :: t, r => if x = r then t else x :: dropHandle t r

/-- Releasing a handle lowers that reference's count by one, and never below
zero. -/
theorem dropHandle_count_self (l : List Ref) (r : Ref) :
    (dropHandle l r).count r = l.count r - 1 := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      by_cases h : x = r
      · rw [h, show dropHandle (r :: t) r = t from by simp [dropHandle], List.count_cons_self]
        omega
      · rw [show dropHandle (x :: t) r = x :: dropHandle t r from by simp [dropHandle, h],
          List.count_cons_of_ne (b := x) (a := r) h,
          List.count_cons_of_ne (b := x) (a := r) h, ih]

/-- Another reference's count is untouched by the release. -/
theorem dropHandle_count_of_ne {x r : Ref} (h : x ≠ r) (l : List Ref) :
    (dropHandle l r).count x = l.count x := by
  induction l with
  | nil => rfl
  | cons y t ih =>
      by_cases hy : y = r
      · rw [hy, show dropHandle (r :: t) r = t from by simp [dropHandle],
          List.count_cons_of_ne (b := r) (a := x) (fun hh => h hh.symm)]
      · by_cases hyx : y = x
        · have hxr : x ≠ r := fun hh => hy (hyx.trans hh)
          rw [hyx, show dropHandle (x :: t) r = x :: dropHandle t r from by simp [dropHandle, hxr],
            List.count_cons_self, List.count_cons_self, ih]
        · rw [show dropHandle (y :: t) r = y :: dropHandle t r from by simp [dropHandle, hy],
            List.count_cons_of_ne (b := y) (a := x) hyx,
            List.count_cons_of_ne (b := y) (a := x) hyx, ih]

/-- Releasing a handle cannot raise any count. -/
theorem dropHandle_count_le (l : List Ref) (r : Ref) (x : Ref) :
    (dropHandle l r).count x ≤ l.count x := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons y t ih =>
      by_cases hy : y = r
      · rw [hy, show dropHandle (r :: t) r = t from by simp [dropHandle]]
        by_cases hx : r = x
        · rw [hx, List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (b := r) (a := x) hx]
          exact Nat.le_refl _
      · by_cases hyx : y = x
        · have hxr : x ≠ r := fun hh => hy (hyx.trans hh)
          rw [hyx, show dropHandle (x :: t) r = x :: dropHandle t r from by
                simp [dropHandle, hxr],
            List.count_cons_self, List.count_cons_self]
          omega
        · rw [show dropHandle (y :: t) r = y :: dropHandle t r from by simp [dropHandle, hy],
            List.count_cons_of_ne (b := y) (a := x) hyx,
            List.count_cons_of_ne (b := y) (a := x) hyx]
          exact ih

/-! ## The three operations

Each is stated as the pair of the heap and the handles it returns, and each
preserves `Counted` from a `Counted` input under its own premise. -/

/-- Allocation: a fresh cell carrying the slots `ks` with count one, the cells
`ks` names raised by the occurrences the new cell contributes, and the new handle
handed out.

Its premises: the reference is not one the heap already lists, the new slots do
not name the cell itself, and every reference `ks` names is a live cell. -/
def alloc (c : CHeap) (handles : List Ref) (r : Ref) (ks : List Ref) : CHeap × List Ref :=
  ((r, cellOf ks) :: CHeap.addOccurrences c ks, r :: handles)

/-- The runtime's increment: a second handle names the existing reference `r`, so
the heap's count for it rises by one. -/
def dup (c : CHeap) (handles : List Ref) (r : Ref) : CHeap × List Ref :=
  (CHeap.adjust c r (· + 1), r :: handles)

/-- The runtime's drop: one handle on `r` is released, so the heap's count for it
falls by one. -/
def drop (c : CHeap) (handles : List Ref) (r : Ref) : CHeap × List Ref :=
  (CHeap.adjust c r (· - 1), dropHandle handles r)

/-- Allocation preserves `Counted`. -/
theorem counted_alloc {c : CHeap} {handles : List Ref} (hc : Counted c handles) {r : Ref}
    {ks : List Ref} (hfresh : r ∉ CHeap.refs c) (hks : r ∉ ks)
    (hlive : ∀ x ∈ ks, x ∈ CHeap.refs c) :
    Counted (alloc c handles r ks).1 (alloc c handles r ks).2 := by
  have hcs : ∀ x, CHeap.count c x = (CHeap.slots c).count x + handles.count x :=
    (counted_iff_slots c handles).mp hc
  simp only [alloc]
  rw [counted_iff_slots]
  intro x
  rw [CHeap.slots_cons, cellOf_slots, CHeap.slots_addOccurrences, List.count_append]
  by_cases hx : x = r
  · rw [hx]
    have hks0 : ks.count r = 0 := List.count_eq_zero.mpr hks
    have hs0 : (CHeap.slots c).count r = 0 := Counted.slots_count_eq_zero hc hfresh
    have hh0 : handles.count r = 0 := Counted.handles_count_eq_zero hc hfresh
    rw [CHeap.count_cons_self, cellOf_count, List.count_cons_self]
    omega
  · rw [CHeap.count_cons_of_ne (by exact fun hh => hx hh.symm),
      List.count_cons_of_ne (b := r) (a := x) (by exact fun hh => hx hh.symm)]
    by_cases hxr : x ∈ CHeap.refs c
    · rw [CHeap.count_addOccurrences_mem c ks hxr, hcs x]
      omega
    · have hks0 : ks.count x = 0 := List.count_eq_zero.mpr (fun hkx => hxr (hlive x hkx))
      have hs0 : (CHeap.slots c).count x = 0 := Counted.slots_count_eq_zero hc hxr
      have hh0 : handles.count x = 0 := Counted.handles_count_eq_zero hc hxr
      rw [CHeap.count_addOccurrences_not_mem c ks hxr]
      omega

/-- The runtime's increment preserves `Counted`: the count it raises and the
handle it adds name the same reference. -/
theorem counted_dup {c : CHeap} {handles : List Ref} (hc : Counted c handles) {r : Ref}
    (hr : r ∈ CHeap.refs c) : Counted (dup c handles r).1 (dup c handles r).2 := by
  have hcs : ∀ x, CHeap.count c x = (CHeap.slots c).count x + handles.count x :=
    (counted_iff_slots c handles).mp hc
  simp only [dup]
  rw [counted_iff_slots]
  intro x
  rw [CHeap.slots_adjust]
  by_cases hx : x = r
  · have hcr : CHeap.count c r = (CHeap.slots c).count r + handles.count r := hcs r
    rw [hx, CHeap.count_adjust_self c r (· + 1) hr, List.count_cons_self]
    omega
  · rw [CHeap.count_adjust_of_ne c r (· + 1) hx,
      List.count_cons_of_ne (b := r) (a := x) (by exact fun hh => hx hh.symm), hcs x]

/-- The runtime's drop preserves `Counted`: the count it lowers and the handle it
releases name the same reference.

Its premise: the handle list holds a handle on `r`, so the drop has one to
release. -/
theorem counted_drop {c : CHeap} {handles : List Ref} (hc : Counted c handles) {r : Ref}
    (hhandle : 1 ≤ handles.count r) : Counted (drop c handles r).1 (drop c handles r).2 := by
  have hcs : ∀ x, CHeap.count c x = (CHeap.slots c).count x + handles.count x :=
    (counted_iff_slots c handles).mp hc
  have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by rw [hcs r]; omega)
  simp only [drop]
  rw [counted_iff_slots]
  intro x
  rw [CHeap.slots_adjust]
  by_cases hx : x = r
  · have hcr : CHeap.count c r = (CHeap.slots c).count r + handles.count r := hcs r
    rw [hx, CHeap.count_adjust_self c r (· - 1) hr, dropHandle_count_self]
    omega
  · rw [CHeap.count_adjust_of_ne c r (· - 1) hx, dropHandle_count_of_ne hx, hcs x]

/-- The destructive write preserves `Counted`.

Its premises: the written cell is live, the write's new slots do not name it, it
did not already name itself, and every reference `ks` names is a live cell. -/
theorem counted_writeSlots {c : CHeap} {handles : List Ref} (hc : Counted c handles) {r : Ref}
    {ks : List Ref} (hr : r ∈ CHeap.refs c) (hks : r ∉ ks) (hself : r ∉ CHeap.slotsAt c r)
    (hlive : ∀ x ∈ ks, x ∈ CHeap.refs c) : Counted (CHeap.writeSlots c r ks) handles := by
  have hcs : ∀ x, CHeap.count c x = (CHeap.slots c).count x + handles.count x :=
    (counted_iff_slots c handles).mp hc
  rw [counted_iff_slots]
  intro x
  rw [CHeap.count_slots_writeSlots c r ks hr x]
  by_cases hx : x = r
  · have hks0 : ks.count r = 0 := List.count_eq_zero.mpr hks
    have hself0 : (CHeap.slotsAt c r).count r = 0 := List.count_eq_zero.mpr hself
    have hcr : CHeap.count c r = (CHeap.slots c).count r + handles.count r := hcs r
    rw [hx, CHeap.count_writeSlots_self c r ks hr]
    omega
  · by_cases hxr : x ∈ CHeap.refs c
    · rw [CHeap.count_writeSlots_of_ne c r ks hx hxr hr, hcs x]
      have hbound := CHeap.slotsAt_count_le_slots c r hr x
      omega
    · have hks0 : ks.count x = 0 := List.count_eq_zero.mpr (fun hkx => hxr (hlive x hkx))
      have hs0 : (CHeap.slots c).count x = 0 := Counted.slots_count_eq_zero hc hxr
      have hh0 : handles.count x = 0 := Counted.handles_count_eq_zero hc hxr
      rw [CHeap.count_writeSlots_not_mem c r ks hxr]
      omega

/-! ## The update and its two branches

`update` is the operation the lowering performs at one cell. Its branch is the
heap's own count at that cell: at one the write is destructive and the cell keeps
its location, and otherwise the updated slots land at a fresh location while the
old cell keeps its slots and loses a reference. -/

/-- The update the lowering performs: when the cell's count is one the write is
destructive and the cell keeps its location; otherwise the result is a fresh cell
and the old one loses a reference. -/
def update (c : CHeap) (handles : List Ref) (r : Ref) (ks : List Ref) : CHeap × List Ref :=
  if CHeap.count c r = 1 then
    (CHeap.writeSlots c r ks, handles)
  else
    ((fresh c ks, cellOf ks) :: CHeap.addOccurrences (CHeap.adjust c r (· - 1)) ks,
      fresh c ks :: dropHandle handles r)

/-- The update at a cell whose count is one: the destructive branch. -/
theorem update_of_count_one (c : CHeap) (handles : List Ref) (r : Ref) (ks : List Ref)
    (h : CHeap.count c r = 1) :
    update c handles r ks = (CHeap.writeSlots c r ks, handles) := by
  simp [update, h]

/-- The update at a cell whose count is not one: the copying branch. -/
theorem update_of_count_ne_one (c : CHeap) (handles : List Ref) (r : Ref) (ks : List Ref)
    (h : CHeap.count c r ≠ 1) :
    update c handles r ks =
      ((fresh c ks, cellOf ks) :: CHeap.addOccurrences (CHeap.adjust c r (· - 1)) ks,
        fresh c ks :: dropHandle handles r) := by
  simp [update, h]

/-- Under a count of one the write is destructive, and the updated slots are read
back at the same location. -/
theorem update_preserves_location_of_exclusive {c : CHeap} {handles : List Ref}
    (hc : Counted c handles) {r : Ref} {ks : List Ref}
    (h1 : Exclusive (CHeap.presentation c) handles r) :
    (update c handles r ks).1.lookup r = some ks := by
  have h1' : CHeap.count c r = 1 := (counted_iff_exclusive hc r).mpr h1
  have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by omega)
  rw [update_of_count_one c handles r ks h1']
  exact CHeap.lookup_writeSlots_self c r ks hr

/-- Under a count that is not one the write copies: the updated slots are read
back at a location the heap did not list, the old cell's slots are untouched, the
old cell's count has fallen by one, and the fresh location is not one the heap
listed. -/
theorem update_copies_of_shared {c : CHeap} {handles : List Ref} (hc : Counted c handles)
    {r : Ref} {ks : List Ref} (h2 : ¬ Exclusive (CHeap.presentation c) handles r)
    (hhandle : 1 ≤ handles.count r) (hks : r ∉ ks) :
    (update c handles r ks).1.lookup (fresh c ks) = some ks ∧
      (update c handles r ks).1.lookup r = CHeap.lookup c r ∧
      (update c handles r ks).1.count r = CHeap.count c r - 1 ∧
      fresh c ks ∉ CHeap.refs c := by
  have hcs : ∀ x, CHeap.count c x = (CHeap.slots c).count x + handles.count x :=
    (counted_iff_slots c handles).mp hc
  have hn1 : CHeap.count c r ≠ 1 := fun h => h2 ((counted_iff_exclusive hc r).mp h)
  have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by rw [hcs r]; omega)
  have hfr : fresh c ks ≠ r := fresh_ne_of_mem_refs hr
  rw [update_of_count_ne_one c handles r ks hn1]
  refine ⟨?_, ?_, ?_, fresh_not_mem_refs c ks⟩
  · simp only [CHeap.lookup_cons_self, cellOf_slots]
  · rw [CHeap.lookup_cons_of_ne (by simpa using hfr), CHeap.lookup_addOccurrences,
      CHeap.lookup_adjust]
  · rw [CHeap.count_cons_of_ne (by simpa using hfr),
      CHeap.count_addOccurrences_mem _ _ (by rw [CHeap.refs_adjust]; exact hr),
      CHeap.count_adjust_self c r (· - 1) hr, List.count_eq_zero.mpr hks]
    omega

/-- The destructive branch preserves `Counted`. -/
theorem counted_update_exclusive {c : CHeap} {handles : List Ref} (hc : Counted c handles)
    {r : Ref} {ks : List Ref} (h1 : Exclusive (CHeap.presentation c) handles r) (hks : r ∉ ks)
    (hself : r ∉ CHeap.slotsAt c r) (hlive : ∀ x ∈ ks, x ∈ CHeap.refs c) :
    Counted (update c handles r ks).1 (update c handles r ks).2 := by
  have h1' : CHeap.count c r = 1 := (counted_iff_exclusive hc r).mpr h1
  have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by omega)
  rw [update_of_count_one c handles r ks h1']
  exact counted_writeSlots hc hr hks hself hlive

/-- The copying branch preserves `Counted`: the fresh cell's count and its one
handle, the old cell's count and its released handle, and the cells `ks` names all
move together. -/
theorem counted_update_copy {c : CHeap} {handles : List Ref} (hc : Counted c handles) {r : Ref}
    {ks : List Ref} (h2 : ¬ Exclusive (CHeap.presentation c) handles r)
    (hhandle : 1 ≤ handles.count r) (hks : r ∉ ks)
    (hlive : ∀ x ∈ ks, x ∈ CHeap.refs c) :
    Counted (update c handles r ks).1 (update c handles r ks).2 := by
  have hcs : ∀ x, CHeap.count c x = (CHeap.slots c).count x + handles.count x :=
    (counted_iff_slots c handles).mp hc
  have hn1 : CHeap.count c r ≠ 1 := fun h => h2 ((counted_iff_exclusive hc r).mp h)
  have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by rw [hcs r]; omega)
  have hfr : fresh c ks ≠ r := fresh_ne_of_mem_refs hr
  have hNot : fresh c ks ∉ CHeap.refs c := fresh_not_mem_refs c ks
  have hs0 : (CHeap.slots c).count (fresh c ks) = 0 := Counted.slots_count_eq_zero hc hNot
  have hh0 : handles.count (fresh c ks) = 0 := Counted.handles_count_eq_zero hc hNot
  have hk0 : ks.count (fresh c ks) = 0 := List.count_eq_zero.mpr (fresh_not_mem_ks c ks)
  have hr0 : CHeap.count c r = (CHeap.slots c).count r + handles.count r := hcs r
  rw [update_of_count_ne_one c handles r ks hn1, counted_iff_slots]
  intro x
  rw [CHeap.slots_cons, cellOf_slots, CHeap.slots_addOccurrences, CHeap.slots_adjust,
    List.count_append]
  by_cases hx : x = fresh c ks
  · rw [hx, CHeap.count_cons_self, cellOf_count, hk0, hs0, List.count_cons_self]
    have hle := dropHandle_count_le handles r (fresh c ks)
    rw [hh0] at hle
    omega
  · rw [CHeap.count_cons_of_ne (by exact fun hh => hx hh.symm),
      List.count_cons_of_ne (b := fresh c ks) (a := x) (by exact fun hh => hx hh.symm)]
    by_cases hxr : x = r
    · rw [hxr]
      have hks0 : ks.count r = 0 := List.count_eq_zero.mpr hks
      rw [CHeap.count_addOccurrences_mem _ _ (by rw [CHeap.refs_adjust]; exact hr),
        CHeap.count_adjust_self c r (· - 1) hr, hks0, dropHandle_count_self]
      omega
    · by_cases hxmem : x ∈ CHeap.refs c
      · rw [CHeap.count_addOccurrences_mem _ _ (by rw [CHeap.refs_adjust]; exact hxmem),
          CHeap.count_adjust_of_ne c r (· - 1) hxr, dropHandle_count_of_ne hxr, hcs x]
        omega
      · have hk0 : ks.count x = 0 := List.count_eq_zero.mpr (fun hkx => hxmem (hlive x hkx))
        have hs0' : (CHeap.slots c).count x = 0 := Counted.slots_count_eq_zero hc hxmem
        have hh0' : handles.count x = 0 := Counted.handles_count_eq_zero hc hxmem
        have hle := dropHandle_count_le handles r x
        rw [CHeap.count_addOccurrences_not_mem _ _ (by rw [CHeap.refs_adjust]; exact hxmem),
          hk0, hs0', hh0'] at *
        omega

/-! ## The take-out temporary

The pair a take-out holds — the extracted element and the array it came from —
puts a second handle on the element while the pair is live. The element's count is
then two, so an update below it copies; dropping that handle first restores the
count of one, so the update keeps the location. This is the modelled form of the
trap the in-place check caught in its `layout5-checked-unique` case: the check
fires on a uniquely owned array until the pair is destructured, because the handle
the pair still holds is the second reference to the element. -/

/-- The pair's handle: counting the heap at the handle list `[e, e]` makes the
extracted element's count two, so it is not exclusive there.

`Footprint.pair_needs_the_drop` supplies the two counts at this handle-list
shape, and `Counted` carries them to the heap's own field. -/
theorem takeout_pair_count_two {c : CHeap} {e : Ref} (hc : Counted c [e, e])
    (h0 : (CHeap.presentation c).occurrences e = 0) :
    CHeap.count c e = 2 ∧ ¬ Exclusive (CHeap.presentation c) [e, e] e := by
  have h := pair_needs_the_drop (CHeap.presentation c) e h0
  refine ⟨?_, ?_⟩
  · rw [hc e, h.1]
  · unfold Exclusive
    rw [h.1]
    omega

/-- The drop of the pair's handle: with one handle left the element's count is
one, so it is exclusive again. -/
theorem takeout_dropped_count_one {c : CHeap} {e : Ref} (hc : Counted c [e, e])
    (h0 : (CHeap.presentation c).occurrences e = 0) :
    (drop c [e, e] e).1.count e = 1 ∧
      Exclusive (CHeap.presentation (drop c [e, e] e).1) (drop c [e, e] e).2 e := by
  have h := pair_needs_the_drop (CHeap.presentation c) e h0
  have htwo : CHeap.count c e = 2 := by rw [hc e, h.1]
  have hdrop := counted_drop hc (r := e) (by simp)
  have hcount : CHeap.count (drop c [e, e] e).1 e = 1 := by
    have hr : e ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by rw [htwo]; omega)
    simp only [drop]
    rw [CHeap.count_adjust_self c e (· - 1) hr, htwo]
  exact ⟨hcount, (counted_iff_exclusive hdrop e).mp hcount⟩

/-- The pair read at the update's decision: with the pair's handle still held the
update below the element copies to a fresh location, and with the handle dropped
first the same update keeps the location.

The drop is what the take-out does when it destructures the pair, and it is what
turns the update below it from the copying branch back to the destructive one. -/
theorem takeout_pair_update_branches {c : CHeap} {e : Ref} {ks : List Ref}
    (hc : Counted c [e, e]) (h0 : (CHeap.presentation c).occurrences e = 0) (hks : e ∉ ks) :
    (update c [e, e] e ks).1.lookup (fresh c ks) = some ks ∧
      (update (drop c [e, e] e).1 (drop c [e, e] e).2 e ks).1.lookup e = some ks := by
  refine ⟨(update_copies_of_shared hc (takeout_pair_count_two hc h0).2 (by simp) hks).1, ?_⟩
  have h1 := (takeout_dropped_count_one hc h0).1
  have he : e ∈ CHeap.refs (drop c [e, e] e).1 :=
    CHeap.mem_refs_of_count_pos _ (by rw [h1]; omega)
  rw [update_of_count_one _ _ e ks h1]
  exact CHeap.lookup_writeSlots_self _ e ks he

end RCHeap
end Scidonia.FracPerm.StateVar
