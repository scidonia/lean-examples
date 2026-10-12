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

`Counted` is stated at a reference and reads the first cell the heap lists there,
so a second cell at the same reference would leave the statement short of the
cell it does not read. Two invariants close that: `CHeap.WF`, the references a
heap lists are duplicate-free, under which the first cell at a reference is the
only one — and `CHeap.Live`, no cell a heap lists carries a count of zero, which is
what an operation's result has to satisfy because the runtime deallocates such a
cell rather than leaving it listed. Every theorem below carries the one its proof
reads, and each operation proves its result has both.

## What is proved

* that under the invariant and `Counted` every cell a heap lists carries its
  aliasing count — `counted_cell_count`: the cell's own `count` field is the
  slot occurrences and the handles that name its reference. This is the statement
  the first-entry reading is not enough for: two cells at one reference could
  disagree, and a heap that lists one twice fails the invariant.
* the bridge `counted_iff_exclusive`: under `Counted`, a cell's count being one
  and `Footprint.Exclusive` at it are the same statement.
* the operations the runtime performs on a count, each preserving the invariant,
  liveness and `Counted` from a heap that has them and under the operation's own
  premise: `alloc`, a fresh cell with its slot list, count one and the new handle
  handed out; `dup`, the runtime's increment, a second handle naming the reference
  and the count up by one; `decRef`, the runtime's non-final decrement, one handle
  released and the count down by one, whose premise is that the count stands at
  two or more, so no count reaches zero through it; and `release`, the final
  release at a count of one, which deallocates the cell and drops the references
  its slots held.
* the update in its two branches, as the model of the lowering's
  `isExclusiveUnsafe` / `lean_array_uset` decision: when the cell's count is one
  the write is destructive, the cell keeps its location, and the references its
  old slots held are dropped — the cells whose counts that brings to zero being
  freed — and otherwise the updated slots land at a fresh location while the old
  cell keeps its slots and loses a reference
  (`update_preserves_location_of_exclusive`, `update_copies_of_shared`). Both
  branches preserve the invariant, liveness and `Counted`.
* the take-out pair at the counted heap: the pair's second handle on the
  extracted element makes its count two, so an update below it copies, and a
  decrement of that handle first restores the count of one, so the update keeps
  the location (`takeout_pair_count_two`, `takeout_dropped_count_one`,
  `takeout_pair_update_branches`).

## What is modelled

A location here is a `Ref`: a name in a list, not a machine address. Two heaps
never share one, and nothing here says where a cell lives. The location a copied
cell takes is a model location, chosen beyond every reference the heap and the
new slots mention; it is a name, not an allocator's answer.

The count is the runtime's count *modelled*: a `Nat` that `Counted` ties to
aliasing, not the machine word an object carries. The split between `decRef` and
`release` is the runtime's own split. `RefCount.decRef`
(`Scidonia/FracPerm/StateVar/RefCount.lean:353`) tests `rc > 1` and lowers the
count there, and for a count that is not above one it takes the cold path
`RefCount.decRefCold` (`RefCount.lean:334`); `decRef_spec`
(`RefCount.lean:358-366`) states that test at the counter level. The cold path is
the branch that frees an object, so this module models it as its own operation:
`lean_dec_ref`'s `else` branch calls `lean_dec_ref_cold`, which deallocates the
object and drops the references its slots held. `decRef` here is the `rc > 1`
branch alone and `release` is the cold path, and the two do not have one behaviour
between them: the count never reaches zero through `decRef`, and `release` never
merely lowers one.

`release`'s outgoing effects are the cascade. `CHeap.dealloc` removes the cell and
lowers the counts of the cells its slots named by the occurrences it contributed —
one drop per occurrence, which is what the runtime's walk over the slots does —
and `CHeap.cascade` repeats the deallocation while any listed cell carries a
count of zero, so a reference the released cell named is dropped by this same
operation and the cell it names is freed when its own count reaches zero. The
repetition is `CHeap.cascadeSteps`, a recursion on the number of steps that a
concrete heap's cascade is a value of, run for as many steps as the heap has
cells — enough, because a step that deallocates removes one. The order in which
the cascade deallocates is the heap's own list order; what is modelled is the heap
it leaves, in which no listed cell carries a count of zero and every count is the
occurrences and handles that remain. A release therefore leaves no orphaned
occurrence: a reference a freed cell named is dropped with it.

The two branches of `update` are the model of the lowering's
`isExclusiveUnsafe` / `lean_array_uset` decision, and the model's decision is the
heap's own count being one. The counts an operation moves are moved together
with the occurrences they count: `writeSlots` takes the written
cell's old slots out of the counts of the cells those slots named and puts `ks`
in, and `addOccurrences` adds the occurrences a new cell's slots contribute. Each
operation also carries the premises that make it well defined at the heap it is
applied to — a fresh cell's reference is not already listed, a slot names a live
cell, a release takes a handle the handle list holds, the written cell does not
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
updates in place, not that a copy happens when it does not, not that a compiled
release frees anything, and nothing about Lean's object graph, its allocation, or
the compiler's reset/reuse pass. The `release` this module models is a removal
from a list of names and a movement of the counts that name it; no memory is
reclaimed and nothing is weak, finalised or resurrected. The counts are logical
counts of occurrences, the locations are names, and the run-time evidence for the
copy-or-mutate behaviour of a compiled write stays where it was, in the in-place
check of `FracPerm`.

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

The list is read as exactly the live cells, as a `Footprint` presentation is, and
`CHeap.WF` below is what makes that reading a property of the heap rather than a
convention: the references a heap lists are duplicate-free, so the first cell a
heap lists at a reference is the only cell it lists there, and `CHeap.lookup` and
`CHeap.count` read the whole story at that reference. A heap that listed one
reference twice fails `CHeap.WF`, which is why the two cells could disagree about
the count and neither would be the count the heap keeps. -/
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

/-- A heap that lists no cell at `r` reads no slots there. -/
theorem CHeap.slotsAt_of_not_mem {c : CHeap} {r : Ref} (h : r ∉ CHeap.refs c) :
    CHeap.slotsAt c r = [] := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      have hr : r' ≠ r := fun hh => h (by simp [CHeap.refs_cons, hh])
      have ht : r ∉ CHeap.refs t := fun hmem => h (by simp [CHeap.refs_cons, hmem])
      rw [CHeap.slotsAt_cons_of_ne hr, ih ht]

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

/-! ## The invariant and liveness

Two statements about a heap's structure, and the two together. `CHeap.WF` is the
one the projections need: the references a heap lists are duplicate-free, so the
first cell it lists at a reference is the only one and `CHeap.count` reads a cell
rather than a choice among cells. Every theorem below whose proof reads a cell out
of the list carries it. `CHeap.Live` is the one an operation's result needs: the
runtime's cold path deallocates a cell whose count has reached zero, so a heap that
still listed one would be a heap a run cannot leave behind. Every operation below
proves both of its result, and the theorems that need both take them as
`CHeap.Healthy`. -/

/-- The invariant: the references a heap lists are duplicate-free, so no reference
names two cells.

Under it `CHeap.count` and `CHeap.slotsAt` read a cell and not the first of
several, and a listed cell's own count is what the heap keeps at its reference
(`CHeap.count_of_mem`). -/
def CHeap.WF (c : CHeap) : Prop := (CHeap.refs c).Nodup

/-- Liveness: no cell a heap lists carries a count of zero.

The form is the one the cascade's own stopping test is — no listed cell matches
the zero-count pattern — which is also what makes the predicate decidable at a
concrete heap. `CHeap.live_iff_count_ne_zero` reads it as the statement it is
meant to be. -/
def CHeap.Live (c : CHeap) : Prop := c.find? (fun e => e.2.count == 0) = none

/-- The two invariants together: the hypothesis of the theorems whose proof reads
both a cell out of the list and the heap as a live one. -/
def CHeap.Healthy (c : CHeap) : Prop := CHeap.WF c ∧ CHeap.Live c

/-- Liveness, as the statement it is meant to be: no listed cell's count is zero. -/
theorem CHeap.live_iff_count_ne_zero (c : CHeap) :
    CHeap.Live c ↔ ∀ e ∈ c, e.2.count ≠ 0 := by
  rw [CHeap.Live, List.find?_eq_none]
  constructor
  · intro h e he hc
    exact h e he (by simp [hc])
  · intro h e he hb
    exact h e he (Nat.beq_eq.mp hb)

/-- Liveness, with the counts read as positive. -/
theorem CHeap.live_iff_count_pos (c : CHeap) :
    CHeap.Live c ↔ ∀ e ∈ c, 0 < e.2.count := by
  rw [CHeap.live_iff_count_ne_zero]
  exact forall_congr' fun _ => forall_congr' fun _ => Nat.pos_iff_ne_zero.symm

/-- The invariant read off the heap's own cells: a heap is well formed exactly when
each reference it lists is followed by no cell that carries it too. -/
theorem CHeap.wf_cons_iff {r : Ref} {cl : Cell} {t : CHeap} :
    CHeap.WF ((r, cl) :: t) ↔ r ∉ CHeap.refs t ∧ CHeap.WF t := by
  simp [CHeap.WF, CHeap.refs_cons, List.nodup_cons]

/-- An empty heap is well formed. -/
theorem CHeap.wf_nil : CHeap.WF ([] : CHeap) := by simp [CHeap.WF]

/-- Under the invariant, the cell a heap lists at `r` carries the count the heap
keeps at `r`: there is one such cell and `CHeap.count` reads it. -/
theorem CHeap.count_of_mem {c : CHeap} {r : Ref} {cl : Cell} (hW : CHeap.WF c)
    (h : (r, cl) ∈ c) : CHeap.count c r = cl.count := by
  induction c with
  | nil => simp at h
  | cons e t ih =>
      obtain ⟨r', cl'⟩ := e
      rw [CHeap.wf_cons_iff] at hW
      rcases List.mem_cons.mp h with heq | hmem
      · have h1 : r = r' := congrArg Prod.fst heq
        have h2 : cl = cl' := congrArg Prod.snd heq
        rw [h1, h2, CHeap.count_cons_self]
      · have hmem' : r ∈ CHeap.refs t := by
          show r ∈ t.map (fun e => e.1)
          exact List.mem_map_of_mem hmem
        have hne : r ≠ r' := fun hh => hW.1 (hh ▸ hmem')
        rw [CHeap.count_cons_of_ne (by exact fun hh => hne hh.symm) cl' t]
        exact ih hW.2 hmem

/-- Liveness read at the references a heap lists: under the invariant, every
reference the heap lists has a positive count. -/
theorem CHeap.live_iff_refs {c : CHeap} (hW : CHeap.WF c) :
    CHeap.Live c ↔ ∀ r ∈ CHeap.refs c, 0 < CHeap.count c r := by
  rw [CHeap.live_iff_count_pos]
  constructor
  · intro h r hr
    induction c with
    | nil => simp [CHeap.refs] at hr
    | cons e t ih =>
        obtain ⟨r', cl⟩ := e
        rw [CHeap.wf_cons_iff] at hW
        by_cases heq : r' = r
        · rw [← heq, CHeap.count_cons_self]
          exact h (r', cl) (List.mem_cons_self ..)
        · have hr' : r ∈ CHeap.refs t :=
            CHeap.mem_refs_cons_of_ne hr (by exact fun hh => heq hh.symm)
          rw [CHeap.count_cons_of_ne heq cl t]
          exact ih hW.2 (fun x hx => h x (List.mem_cons_of_mem _ hx)) hr'
  · intro h e he
    rw [← CHeap.count_of_mem hW he]
    exact h e.1 (by
      show e.1 ∈ c.map (fun e => e.1)
      exact List.mem_map_of_mem he)

/-- A well-formed heap is a heap of this invariant. -/
theorem CHeap.Healthy.wf {c : CHeap} (h : CHeap.Healthy c) : CHeap.WF c := h.1

/-- A heap of this invariant is live. -/
theorem CHeap.Healthy.live {c : CHeap} (h : CHeap.Healthy c) : CHeap.Live c := h.2

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
and its handle list name only live cells.

`Counted` is stated at a reference and `CHeap.count` reads the first cell the heap
lists there. Under `CHeap.WF` that is the only cell at the reference, and
`counted_cell_count` reads the statement back at every listed cell's own `count`
field, which is what makes the field a fact about the aliasing rather than a
number that could differ from the count the heap keeps. -/
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

/-- Under the invariant and `Counted`, every cell a heap lists carries its aliasing
count: the cell's own `count` field is what `Footprint` counts for its reference —
its slot occurrences among the live cells plus the outside handles that name it.

`Counted` is a statement about references and `CHeap.count` reads the first cell at
one, so this is what ties the two together: with the invariant there is only that
cell, and its field is not free of the aliasing. Two cells at one reference could
disagree here — and a heap that lists one twice fails the invariant, which is why
the disagreement is not a state this module states anything about. -/
theorem counted_cell_count {c : CHeap} {handles : List Ref} (hW : CHeap.WF c)
    (hc : Counted c handles) {r : Ref} {cl : Cell} (h : (r, cl) ∈ c) :
    cl.count = refCount (CHeap.presentation c) handles r := by
  rw [← CHeap.count_of_mem hW h]
  exact hc r

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

/-- Moving a whole heap's cells keeps its references. -/
theorem CHeap.refs_map_shiftCell (c : CHeap) (old ks : List Ref) :
    CHeap.refs (c.map (shiftCell old ks)) = CHeap.refs c := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      rw [List.map_cons, shiftCell_pair, CHeap.refs_cons, CHeap.refs_cons, ih]

/-- The write lists the same references. -/
theorem CHeap.refs_writeSlotsAux (ks : List Ref) (r : Ref) (c : CHeap) :
    CHeap.refs (CHeap.writeSlotsAux ks r c) = CHeap.refs c := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · rw [h, CHeap.writeSlotsAux_cons_self, CHeap.refs_cons, CHeap.refs_cons,
          CHeap.refs_map_shiftCell]
      · rw [CHeap.writeSlotsAux_cons_of_ne h, shiftCell_pair, CHeap.refs_cons, CHeap.refs_cons,
          ih]

/-- The write lists the same references. -/
theorem CHeap.refs_writeSlots (c : CHeap) (r : Ref) (ks : List Ref) :
    CHeap.refs (CHeap.writeSlots c r ks) = CHeap.refs c :=
  CHeap.refs_writeSlotsAux ks r c

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

/-- A handle list whose head is the released reference drops that head. -/
@[simp] theorem dropHandle_cons_self (t : List Ref) (r : Ref) : dropHandle (r :: t) r = t := by
  simp [dropHandle]

/-- A handle list whose head is another reference keeps it and drops from the
tail. -/
@[simp] theorem dropHandle_cons_of_ne {r' : Ref} (h : r' ≠ r) (t : List Ref) :
    dropHandle (r' :: t) r = r' :: dropHandle t r := by
  simp [dropHandle, h]

/-- A reference the handle list does not hold is one the release leaves out too. -/
theorem dropHandle_not_mem_of_not_mem {l : List Ref} {x r : Ref} (h : x ∉ l) :
    x ∉ dropHandle l r := by
  induction l with
  | nil => simp [dropHandle]
  | cons y t ih =>
      have hx : x ≠ y := fun hh => h (by rw [hh]; exact List.mem_cons_self ..)
      have ht : x ∉ t := fun hmem => h (List.mem_cons_of_mem y hmem)
      by_cases hy : y = r
      · rw [hy, dropHandle_cons_self]
        exact ht
      · rw [dropHandle_cons_of_ne hy]
        intro hmem
        rcases List.mem_cons.mp hmem with heq | hmem'
        · exact hx heq
        · exact ih ht hmem'

/-- A release removes the released reference from a handle list that holds it
once: a duplicate-free list holds no other occurrence. -/
theorem dropHandle_not_mem_self_of_nodup {l : List Ref} (h : l.Nodup) (r : Ref) :
    r ∉ dropHandle l r := by
  induction l with
  | nil => simp [dropHandle]
  | cons y t ih =>
      have ht : t.Nodup := (List.nodup_cons.mp h).2
      by_cases hy : y = r
      · rw [hy] at h ⊢
        rw [dropHandle_cons_self]
        exact (List.nodup_cons.mp h).1
      · rw [dropHandle_cons_of_ne hy]
        intro hmem
        rcases List.mem_cons.mp hmem with heq | hmem'
        · exact hy heq.symm
        · exact ih ht hmem'

/-- A release keeps a handle list duplicate-free. -/
theorem dropHandle_nodup {l : List Ref} (h : l.Nodup) (r : Ref) : (dropHandle l r).Nodup := by
  induction l with
  | nil => simp [dropHandle]
  | cons y t ih =>
      have ht : t.Nodup := (List.nodup_cons.mp h).2
      by_cases hy : y = r
      · rw [hy, dropHandle_cons_self]
        exact ht
      · rw [dropHandle_cons_of_ne hy]
        exact List.nodup_cons.mpr
          ⟨dropHandle_not_mem_of_not_mem (List.nodup_cons.mp h).1, ih ht⟩

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

/-! ## The deallocation and the drop cascade

The runtime's cold path does not lower a count that stands at one: it frees the
cell. The cell is deallocated and every reference its slots held is dropped, each
drop lowering the named cell's count by the occurrences the freed cell
contributed, and a cell whose own count reaches zero is freed in turn. `dealloc` is
the first half — one cell removed and the counts of the cells its slots named
moved down — and `cascade` is the second, the same step repeated while any listed
cell carries a count of zero. The repetition is on the heap itself: each step
removes one cell and no step raises a count, so `cascade` terminates on the list's
length. -/

/-- The heap with the first cell it lists at `r` removed, and every other cell's
count lowered by the occurrences the removed cell's slots contributed at it.

A cell before the removed one in the list reads the removed cell's slots from the
tail it is followed by, and a cell after it from the removed cell itself; either
way one cell's slots are gone and every other cell's count moves by exactly the
occurrences that name it. A heap that lists no cell at `r` is returned with no
slots changed and its counts moved by the empty list, which is itself. -/
def CHeap.deallocAux (r : Ref) : CHeap → CHeap
  | [] => []
  | (r', cl) :: t =>
      if r' = r then t.map (shiftCell cl.slots [])
      else shiftCell (CHeap.slotsAt t r) [] (r', cl) :: CHeap.deallocAux r t

/-- The heap with the cell it lists at `r` deallocated: the cell removed and every
other cell's count lowered by the occurrences the removed cell's slots contributed
at it.

This is the cell's deallocation, the first half of the runtime's cold path: the
object is freed and each reference its slots held is dropped. A drop that lowers a
cell to zero is not modelled here — it is what `cascade` below continues with. -/
def CHeap.dealloc (c : CHeap) (r : Ref) : CHeap := CHeap.deallocAux r c

/-- The deallocation is the auxiliary recursion on the heap itself. -/
theorem CHeap.dealloc_eq (c : CHeap) (r : Ref) : CHeap.dealloc c r = CHeap.deallocAux r c := rfl

/-- An empty heap has nothing to deallocate. -/
@[simp] theorem CHeap.deallocAux_nil (r : Ref) : CHeap.deallocAux r ([] : CHeap) = [] := rfl

/-- At the removed cell's own reference the deallocation fires: the cell goes and
the tail's counts move. -/
@[simp] theorem CHeap.deallocAux_cons_self (r : Ref) (cl : Cell) (t : CHeap) :
    CHeap.deallocAux r ((r, cl) :: t) = t.map (shiftCell cl.slots []) := by
  simp [CHeap.deallocAux]

/-- At another reference the head's count moves and the tail is searched. -/
@[simp] theorem CHeap.deallocAux_cons_of_ne {r' : Ref} (h : r' ≠ r) (cl : Cell) (t : CHeap) :
    CHeap.deallocAux r ((r', cl) :: t)
      = shiftCell (CHeap.slotsAt t r) [] (r', cl) :: CHeap.deallocAux r t := by
  simp [CHeap.deallocAux, h]

/-- Moving a whole heap's cells keeps the slots read at every reference. -/
theorem CHeap.lookup_map_shiftCell (c : CHeap) (old ks : List Ref) (x : Ref) :
    CHeap.lookup (c.map (shiftCell old ks)) x = CHeap.lookup c x := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      rw [List.map_cons, shiftCell_pair]
      by_cases hx : r' = x
      · rw [← hx, CHeap.lookup_cons_self, CHeap.lookup_cons_self, shiftCount_slots]
      · rw [CHeap.lookup_cons_of_ne hx, CHeap.lookup_cons_of_ne hx, ih]

/-- The deallocation lists the references less one occurrence of the removed
cell's own. -/
theorem CHeap.refs_deallocAux (r : Ref) (c : CHeap) :
    CHeap.refs (CHeap.deallocAux r c) = dropHandle (CHeap.refs c) r := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · rw [h, CHeap.deallocAux_cons_self, CHeap.refs_map_shiftCell, CHeap.refs_cons,
          dropHandle_cons_self]
      · rw [CHeap.deallocAux_cons_of_ne h, shiftCell_pair, CHeap.refs_cons, CHeap.refs_cons,
          dropHandle_cons_of_ne h, ih]

/-- The deallocation lists the references less one occurrence of the removed
cell's own. -/
theorem CHeap.refs_dealloc (c : CHeap) (r : Ref) :
    CHeap.refs (CHeap.dealloc c r) = dropHandle (CHeap.refs c) r :=
  CHeap.refs_deallocAux r c

/-- A heap that lists no cell at `r` is left as it is by the deallocation. -/
theorem CHeap.deallocAux_of_not_mem (r : Ref) {c : CHeap} (h : r ∉ CHeap.refs c) :
    CHeap.deallocAux r c = c := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      have hr : r' ≠ r := fun hh => h (by simp [CHeap.refs_cons, hh])
      have ht : r ∉ CHeap.refs t := fun hmem => h (by simp [CHeap.refs_cons, hmem])
      rw [CHeap.deallocAux_cons_of_ne hr, CHeap.slotsAt_of_not_mem ht, ih ht]
      simp [shiftCell, shiftCount]

/-- A heap that lists no cell at `r` is left as it is by the deallocation. -/
theorem CHeap.dealloc_of_not_mem {c : CHeap} {r : Ref} (h : r ∉ CHeap.refs c) :
    CHeap.dealloc c r = c :=
  CHeap.deallocAux_of_not_mem r h

/-- The deallocation removes one cell from a heap that lists one at `r`. -/
theorem CHeap.length_deallocAux_lt (r : Ref) (c : CHeap) (h : r ∈ CHeap.refs c) :
    (CHeap.deallocAux r c).length < c.length := by
  induction c with
  | nil => simp [CHeap.refs] at h
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases hr : r' = r
      · rw [hr, CHeap.deallocAux_cons_self]
        simp
      · rw [CHeap.deallocAux_cons_of_ne hr]
        have hr' : r ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne h (by exact fun hh => hr hh.symm)
        simp only [List.length_cons]
        have := ih hr'
        omega

/-- The deallocation removes one cell from a heap that lists one at `r`. -/
theorem CHeap.length_dealloc_lt {c : CHeap} {r : Ref} (h : r ∈ CHeap.refs c) :
    (CHeap.dealloc c r).length < c.length :=
  CHeap.length_deallocAux_lt r c h

/-- The deallocation reads another reference's slots as the heap did: the cell at
`r` is the only one it removes. -/
theorem CHeap.lookup_deallocAux_of_ne (r x : Ref) (c : CHeap) (h : x ≠ r) :
    CHeap.lookup (CHeap.deallocAux r c) x = CHeap.lookup c x := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases hr : r' = r
      · rw [hr, CHeap.deallocAux_cons_self, CHeap.lookup_cons_of_ne (by exact fun hh => h hh.symm),
          CHeap.lookup_map_shiftCell]
      · rw [CHeap.deallocAux_cons_of_ne hr, shiftCell_pair]
        by_cases hx : r' = x
        · rw [← hx, CHeap.lookup_cons_self, CHeap.lookup_cons_self, shiftCount_slots]
        · rw [CHeap.lookup_cons_of_ne hx, CHeap.lookup_cons_of_ne hx, ih]

/-- The deallocation reads another reference's slots as the heap did: the cell at
`r` is the only one it removes. -/
theorem CHeap.lookup_dealloc_of_ne (c : CHeap) (r : Ref) {x : Ref} (h : x ≠ r) :
    CHeap.lookup (CHeap.dealloc c r) x = CHeap.lookup c x :=
  CHeap.lookup_deallocAux_of_ne r x c h

/-- A cell the heap lists at another reference than the removed one keeps its own
count less the occurrences the removed cell's slots contributed at it. -/
theorem CHeap.count_dealloc_of_ne (c : CHeap) (r : Ref) {x : Ref} (hx : x ≠ r)
    (hx' : x ∈ CHeap.refs c) (hr : r ∈ CHeap.refs c) :
    CHeap.count (CHeap.dealloc c r) x = CHeap.count c x - (CHeap.slotsAt c r).count x := by
  induction c with
  | nil => simp [CHeap.refs] at hx'
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · have hx'' : x ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne hx' (fun hh => hx (hh.trans h))
        rw [← h, CHeap.dealloc_eq, CHeap.deallocAux_cons_self, CHeap.slotsAt_cons_self,
          CHeap.count_map_shiftCell_mem t cl.slots [] hx'',
          CHeap.count_cons_of_ne (by exact fun hh => hx (hh.symm.trans h))]
        simp
      · have hr' : r ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne hr (by exact fun hh => h hh.symm)
        by_cases hxr : r' = x
        · rw [← hxr, CHeap.dealloc_eq, CHeap.deallocAux_cons_of_ne h, shiftCell_pair,
            CHeap.slotsAt_cons_of_ne h, CHeap.count_cons_self]
          rw [shiftCount_count]
          simp
        · have hx'' : x ∈ CHeap.refs t :=
            CHeap.mem_refs_cons_of_ne hx' (by exact fun hh => hxr hh.symm)
          rw [CHeap.dealloc_eq, CHeap.deallocAux_cons_of_ne h, shiftCell_pair,
            CHeap.count_cons_of_ne hxr, CHeap.slotsAt_cons_of_ne h,
            CHeap.count_cons_of_ne hxr]
          exact ih hx'' hr'

/-- A cell the heap does not list is not read: the deallocation leaves its count
at zero. -/
theorem CHeap.count_dealloc_not_mem (c : CHeap) (r : Ref) {x : Ref}
    (hx : x ∉ CHeap.refs c) : CHeap.count (CHeap.dealloc c r) x = 0 := by
  refine CHeap.count_eq_zero_of_not_mem ?_
  rw [CHeap.refs_dealloc]
  exact dropHandle_not_mem_of_not_mem hx

/-- Under the invariant, a deallocated cell keeps no count: the heap no longer
lists its reference. -/
theorem CHeap.count_dealloc_self {c : CHeap} (hW : CHeap.WF c) (r : Ref) :
    CHeap.count (CHeap.dealloc c r) r = 0 := by
  refine CHeap.count_eq_zero_of_not_mem ?_
  rw [CHeap.refs_dealloc]
  exact dropHandle_not_mem_self_of_nodup hW r

/-- The deallocation removes exactly the occurrences the removed cell's slots
contributed. -/
theorem CHeap.count_slots_dealloc (c : CHeap) (r : Ref) (hr : r ∈ CHeap.refs c) (y : Ref) :
    (CHeap.slots (CHeap.dealloc c r)).count y
      = (CHeap.slots c).count y - (CHeap.slotsAt c r).count y := by
  induction c with
  | nil => simp [CHeap.refs] at hr
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · rw [← h, CHeap.dealloc_eq, CHeap.deallocAux_cons_self, CHeap.slotsAt_cons_self,
          CHeap.slots_map_shiftCell]
        simp only [CHeap.slots_cons, List.count_append]
        omega
      · have hr' : r ∈ CHeap.refs t :=
          CHeap.mem_refs_cons_of_ne hr (by exact fun hh => h hh.symm)
        have hbound := CHeap.slotsAt_count_le_slots t r hr' y
        have hih := ih hr'
        rw [CHeap.dealloc_eq] at hih
        rw [CHeap.dealloc_eq, CHeap.deallocAux_cons_of_ne h, shiftCell_pair,
          CHeap.slotsAt_cons_of_ne h]
        simp only [CHeap.slots_cons, shiftCount_slots, List.count_append]
        omega

/-- The deallocation preserves the invariant: it lists the references less one. -/
theorem CHeap.wf_dealloc {c : CHeap} (hW : CHeap.WF c) (r : Ref) :
    CHeap.WF (CHeap.dealloc c r) := by
  rw [CHeap.WF, CHeap.refs_dealloc]
  exact dropHandle_nodup hW r

/-- The deallocation preserves `Counted` at a cell whose count is zero: such a cell
is named by nothing and its own slots' occurrences are counted already, so removing
the cell and the occurrences it contributed leaves every other count equal to the
occurrences and handles that remain. -/
theorem counted_dealloc {c : CHeap} {handles : List Ref} (hW : CHeap.WF c)
    (hc : Counted c handles) {r : Ref} (h0 : CHeap.count c r = 0) :
    Counted (CHeap.dealloc c r) handles := by
  have hcs : ∀ x, CHeap.count c x = (CHeap.slots c).count x + handles.count x :=
    (counted_iff_slots c handles).mp hc
  by_cases hr : r ∈ CHeap.refs c
  · have hsr : (CHeap.slots c).count r = 0 := by
      have := hcs r
      omega
    have hhr : handles.count r = 0 := by
      have := hcs r
      omega
    have hksr : (CHeap.slotsAt c r).count r = 0 := by
      have := CHeap.slotsAt_count_le_slots c r hr r
      omega
    rw [counted_iff_slots]
    intro x
    by_cases hx : x = r
    · rw [hx, CHeap.count_dealloc_self hW r, CHeap.count_slots_dealloc c r hr r, hsr, hksr,
        hhr]
    · by_cases hxr : x ∈ CHeap.refs c
      · rw [CHeap.count_dealloc_of_ne c r hx hxr hr, CHeap.count_slots_dealloc c r hr x]
        have hbound := CHeap.slotsAt_count_le_slots c r hr x
        have := hcs x
        omega
      · rw [CHeap.count_dealloc_not_mem c r hxr, CHeap.count_slots_dealloc c r hr x,
          Counted.slots_count_eq_zero hc hxr, Counted.handles_count_eq_zero hc hxr]
        have hbound := CHeap.slotsAt_count_le_slots c r hr x
        have hs0 : (CHeap.slots c).count x = 0 := Counted.slots_count_eq_zero hc hxr
        omega
  · rw [CHeap.dealloc_of_not_mem hr]
    exact hc

/-- The cascade's steps: the deallocation repeated while any listed cell carries a
count of zero, one step per count of `n`. A step that finds no counted-zero cell
leaves the heap as it is; a step that finds one deallocates it, and the steps that
remain run on what that leaves. The recursion is on `n`, so a concrete heap's
cascade is a value the kernel reduces. -/
def CHeap.cascadeSteps : Nat → CHeap → CHeap
  | 0, c => c
  | n + 1, c =>
      match c.find? (fun e => e.2.count == 0) with
      | some e => CHeap.cascadeSteps n (CHeap.dealloc c e.1)
      | none => c

/-- The drop cascade: the deallocation repeated for as many steps as the heap has
cells, which is enough — a step that deallocates removes one cell, so a heap of `n`
cells reaches one with no counted-zero cell within `n` steps.

This is the second half of the runtime's cold path. The released cell's
deallocation (`CHeap.dealloc`) lowered the counts of the cells its slots named by
the occurrences it contributed; a cell whose count that brought to zero is
deallocated here, and the references its own slots held are dropped in turn. -/
def CHeap.cascade (c : CHeap) : CHeap := CHeap.cascadeSteps c.length c

/-- A step of the cascade whose heap has no counted-zero cell leaves it as it is. -/
theorem CHeap.cascadeSteps_eq_none {n : Nat} {c : CHeap}
    (h : c.find? (fun e => e.2.count == 0) = none) : CHeap.cascadeSteps (n + 1) c = c := by
  rw [CHeap.cascadeSteps]
  simp [h]

/-- A step of the cascade whose heap has a counted-zero cell deallocates that cell,
and the steps that remain run on what the deallocation leaves. -/
theorem CHeap.cascadeSteps_succ_some {n : Nat} {c : CHeap} {e : Ref × Cell}
    (h : c.find? (fun e => e.2.count == 0) = some e) :
    CHeap.cascadeSteps (n + 1) c = CHeap.cascadeSteps n (CHeap.dealloc c e.1) := by
  rw [CHeap.cascadeSteps]
  simp [h]

/-- The steps preserve the invariant: they remove cells and add none. -/
theorem CHeap.wf_cascadeSteps (n : Nat) {c : CHeap} (hW : CHeap.WF c) :
    CHeap.WF (CHeap.cascadeSteps n c) := by
  induction n generalizing c with
  | zero => exact hW
  | succ n ih =>
      cases hfind : c.find? (fun e => e.2.count == 0) with
      | none => rw [CHeap.cascadeSteps_eq_none hfind]; exact hW
      | some e => rw [CHeap.cascadeSteps_succ_some hfind]; exact ih (CHeap.wf_dealloc hW e.1)

/-- The steps leave no counted-zero cell once they have run for at least as many
steps as the heap has cells: a step that fires removes one cell, and a step that
does not fire leaves the heap. -/
theorem CHeap.live_cascadeSteps (n : Nat) {c : CHeap} (h : c.length ≤ n) :
    CHeap.Live (CHeap.cascadeSteps n c) := by
  induction n generalizing c with
  | zero =>
      cases c with
      | nil => rfl
      | cons e t => simp at h
  | succ n ih =>
      cases hfind : c.find? (fun e => e.2.count == 0) with
      | none => rw [CHeap.cascadeSteps_eq_none hfind]; exact hfind
      | some e =>
          rw [CHeap.cascadeSteps_succ_some hfind]
          have hlt := CHeap.length_dealloc_lt (c := c) (r := e.1)
            (List.mem_map_of_mem (List.mem_of_find?_eq_some hfind))
          exact ih (by omega)

/-- The steps preserve `Counted`: each deallocates a counted-zero cell, which the
deallocation's own theorem covers. -/
theorem counted_cascadeSteps (n : Nat) {c : CHeap} {handles : List Ref} (hW : CHeap.WF c)
    (hc : Counted c handles) : Counted (CHeap.cascadeSteps n c) handles := by
  induction n generalizing c with
  | zero => exact hc
  | succ n ih =>
      cases hfind : c.find? (fun e => e.2.count == 0) with
      | none => rw [CHeap.cascadeSteps_eq_none hfind]; exact hc
      | some e =>
          rw [CHeap.cascadeSteps_succ_some hfind]
          have h0 : CHeap.count c e.1 = 0 := by
            rw [CHeap.count_of_mem hW (List.mem_of_find?_eq_some hfind)]
            exact Nat.beq_eq.mp
              (List.find?_some (p := fun (e : Ref × Cell) => e.2.count == 0) hfind)
          exact ih (CHeap.wf_dealloc hW e.1) (counted_dealloc hW hc h0)

/-- A reference no cell's slots name is one the steps neither remove nor read
differently: no deallocation moves its count, and a cell is removed only when its
own count is zero. -/
theorem CHeap.lookup_cascadeSteps_of_slot_free (n : Nat) {c : CHeap} {r : Ref}
    (hW : CHeap.WF c) (hs : (CHeap.slots c).count r = 0) (hp : 0 < CHeap.count c r) :
    CHeap.lookup (CHeap.cascadeSteps n c) r = CHeap.lookup c r := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      cases hfind : c.find? (fun e => e.2.count == 0) with
      | none => rw [CHeap.cascadeSteps_eq_none hfind]
      | some e =>
          have hWc : CHeap.WF c := hW
          have hsc : (CHeap.slots c).count r = 0 := hs
          have hpc : 0 < CHeap.count c r := hp
          rw [CHeap.cascadeSteps_succ_some hfind]
          have hm : e ∈ c := List.mem_of_find?_eq_some hfind
          have her : e.1 ∈ CHeap.refs c := by
            show e.1 ∈ c.map (fun e => e.1)
            exact List.mem_map_of_mem hm
          have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c hpc
          have hne : e.1 ≠ r := by
            intro heq
            have h0 : CHeap.count c e.1 = 0 := by
              rw [CHeap.count_of_mem hWc hm]
              exact Nat.beq_eq.mp
                (List.find?_some (p := fun (e : Ref × Cell) => e.2.count == 0) hfind)
            rw [heq] at h0
            omega
          have hs' : (CHeap.slots (CHeap.dealloc c e.1)).count r = 0 := by
            rw [CHeap.count_slots_dealloc c e.1 her r, hsc]
            have hbound := CHeap.slotsAt_count_le_slots c e.1 her r
            omega
          have hp' : 0 < CHeap.count (CHeap.dealloc c e.1) r := by
            rw [CHeap.count_dealloc_of_ne c e.1 (Ne.symm hne) hr her]
            have hbound := CHeap.slotsAt_count_le_slots c e.1 her r
            omega
          rw [ih (CHeap.wf_dealloc hWc e.1) hs' hp',
            CHeap.lookup_dealloc_of_ne c e.1 (Ne.symm hne)]

/-- A reference the heap does not list is one the steps leave unlisted: a
deallocation removes a reference rather than adding one. -/
theorem CHeap.count_cascadeSteps_of_not_mem (n : Nat) {c : CHeap} {x : Ref}
    (hx : x ∉ CHeap.refs c) : CHeap.count (CHeap.cascadeSteps n c) x = 0 := by
  induction n generalizing c with
  | zero => exact CHeap.count_eq_zero_of_not_mem hx
  | succ n ih =>
      cases hfind : c.find? (fun e => e.2.count == 0) with
      | none => rw [CHeap.cascadeSteps_eq_none hfind]; exact CHeap.count_eq_zero_of_not_mem hx
      | some e =>
          rw [CHeap.cascadeSteps_succ_some hfind]
          exact ih (by
            rw [CHeap.refs_dealloc]
            exact dropHandle_not_mem_of_not_mem hx)

/-- The cascade preserves the invariant: it removes cells. -/
theorem CHeap.wf_cascade {c : CHeap} (hW : CHeap.WF c) : CHeap.WF (CHeap.cascade c) :=
  CHeap.wf_cascadeSteps c.length hW

/-- The cascade leaves no counted-zero cell: it runs at least as many steps as the
heap has cells, and a step that deallocates removes one. -/
theorem CHeap.live_cascade (c : CHeap) : CHeap.Live (CHeap.cascade c) :=
  CHeap.live_cascadeSteps c.length (Nat.le_refl c.length)

/-- The cascade preserves `Counted`. -/
theorem counted_cascade {c : CHeap} {handles : List Ref} (hW : CHeap.WF c)
    (hc : Counted c handles) : Counted (CHeap.cascade c) handles :=
  counted_cascadeSteps c.length hW hc

/-- A reference no cell's slots name is one the cascade neither removes nor reads
differently. -/
theorem CHeap.lookup_cascade_of_slot_free {c : CHeap} {r : Ref} (hW : CHeap.WF c)
    (hs : (CHeap.slots c).count r = 0) (hp : 0 < CHeap.count c r) :
    CHeap.lookup (CHeap.cascade c) r = CHeap.lookup c r :=
  CHeap.lookup_cascadeSteps_of_slot_free c.length hW hs hp

/-- A reference the heap does not list is one the cascade leaves unlisted: a
deallocation removes a reference rather than adding one. -/
theorem CHeap.count_cascade_of_not_mem {c : CHeap} {x : Ref} (hx : x ∉ CHeap.refs c) :
    CHeap.count (CHeap.cascade c) x = 0 :=
  CHeap.count_cascadeSteps_of_not_mem c.length hx

/-! ## The operations on a count

Each operation is stated as the pair of the heap and the handles it returns. The
runtime's drop is two operations here, because it is two in the runtime: the
`rc > 1` branch lowers a count, and the last handle's release deallocates the
object. `RefCount.decRef` (`RefCount.lean:353`) is the test that splits them —
`if rc > 1 then some (rc - 1) else if rc != 0 then decRefCold rc else some rc`,
which `decRef_spec` (`RefCount.lean:358-366`) states at the counter level — and
`lean_dec_ref`'s cold path is the branch the release models. -/

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

/-- The runtime's non-final decrement: one handle on `r` is released, so the heap's
count for it falls by one.

This is the `rc > 1` branch of `RefCount.decRef` alone. No count reaches zero
through it — the operation's premise is that the count stands at two or more — so
it is not the operation that frees a cell: `release` below is. -/
def decRef (c : CHeap) (handles : List Ref) (r : Ref) : CHeap × List Ref :=
  (CHeap.adjust c r (· - 1), dropHandle handles r)

/-- The runtime's final release: the cell at `r` has count one and one of its
handles is released, so the runtime deallocates the object — the `else` branch of
`RefCount.decRef`, the cold path of `lean_dec_ref`, which frees the cell rather
than lowering its count — and drops every reference the cell's slots held, each
drop freeing the cell it names when that cell's own count reaches zero.

The outgoing effect is the cascade: `CHeap.dealloc` removes the cell and lowers the
counts of the cells its slots named by the occurrences it contributed, and
`CHeap.cascade` repeats it while any listed cell carries a count of zero, so a
reference the released cell named is dropped by this same operation. -/
def release (c : CHeap) (handles : List Ref) (r : Ref) : CHeap × List Ref :=
  (CHeap.cascade (CHeap.dealloc c r), dropHandle handles r)

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

/-- Allocation preserves the invariant: the new reference is not one the heap
listed, so the references stay duplicate-free. -/
theorem CHeap.wf_alloc {c : CHeap} {handles : List Ref} {r : Ref} {ks : List Ref}
    (hW : CHeap.WF c) (hfresh : r ∉ CHeap.refs c) : CHeap.WF (alloc c handles r ks).1 := by
  simp only [alloc]
  rw [CHeap.WF, CHeap.refs_cons, CHeap.refs_addOccurrences]
  exact List.nodup_cons.mpr ⟨hfresh, hW⟩

/-- Allocation preserves liveness: the fresh cell's count is one and the cells `ks`
names have their counts raised, so no listed cell's count is zero. -/
theorem CHeap.live_alloc {c : CHeap} {handles : List Ref} {r : Ref} {ks : List Ref}
    (h : CHeap.Healthy c) (hfresh : r ∉ CHeap.refs c) :
    CHeap.Live (alloc c handles r ks).1 := by
  obtain ⟨hW, hl⟩ := h
  rw [CHeap.live_iff_refs (CHeap.wf_alloc hW hfresh)]
  simp only [alloc, CHeap.refs_cons, CHeap.refs_addOccurrences]
  intro x hx
  by_cases hxr : x = r
  · rw [hxr, CHeap.count_cons_self, cellOf_count]
    omega
  · have hx' : x ∈ CHeap.refs c := by
      rcases List.mem_cons.mp hx with heq | hx'
      · exact absurd heq hxr
      · exact hx'
    rw [CHeap.count_cons_of_ne (by exact fun hh => hxr hh.symm),
      CHeap.count_addOccurrences_mem c ks hx']
    have := (CHeap.live_iff_refs hW).mp hl x hx'
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

/-- The runtime's increment preserves the invariant: it changes no reference. -/
theorem CHeap.wf_dup {c : CHeap} {handles : List Ref} {r : Ref} (hW : CHeap.WF c) :
    CHeap.WF (dup c handles r).1 := by
  simp only [dup]
  rwa [CHeap.WF, CHeap.refs_adjust]

/-- The runtime's increment preserves liveness: it raises one count and leaves the
others. -/
theorem CHeap.live_dup {c : CHeap} {handles : List Ref} {r : Ref} (h : CHeap.Healthy c)
    (hr : r ∈ CHeap.refs c) : CHeap.Live (dup c handles r).1 := by
  obtain ⟨hW, hl⟩ := h
  rw [CHeap.live_iff_refs (CHeap.wf_dup hW)]
  simp only [dup, CHeap.refs_adjust] at *
  intro x hx
  by_cases hxr : x = r
  · rw [hxr, CHeap.count_adjust_self c r (· + 1) hr]
    have := (CHeap.live_iff_refs hW).mp hl r hr
    omega
  · rw [CHeap.count_adjust_of_ne c r (· + 1) hxr]
    exact (CHeap.live_iff_refs hW).mp hl x hx

/-- The runtime's non-final decrement preserves the invariant. -/
theorem CHeap.wf_decRef {c : CHeap} {handles : List Ref} {r : Ref} (hW : CHeap.WF c) :
    CHeap.WF (decRef c handles r).1 := by
  simp only [decRef]
  rwa [CHeap.WF, CHeap.refs_adjust]

/-- The runtime's non-final decrement preserves liveness: its premise is that the
count stands at two or more, so the one it lowers stays positive and no other count
moves. -/
theorem CHeap.live_decRef {c : CHeap} {handles : List Ref} {r : Ref} (h : CHeap.Healthy c)
    (h2 : 2 ≤ CHeap.count c r) : CHeap.Live (decRef c handles r).1 := by
  obtain ⟨hW, hl⟩ := h
  have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by omega)
  rw [CHeap.live_iff_refs (CHeap.wf_decRef hW)]
  simp only [decRef, CHeap.refs_adjust] at *
  intro x hx
  by_cases hxr : x = r
  · rw [hxr, CHeap.count_adjust_self c r (· - 1) hr]
    omega
  · rw [CHeap.count_adjust_of_ne c r (· - 1) hxr]
    exact (CHeap.live_iff_refs hW).mp hl x hx

/-- The runtime's decrement preserves `Counted`: the count it lowers and the handle
it releases name the same reference.

Its premise: the handle list holds a handle on `r`, so the decrement has one to
release. A count that reaches zero is not this operation's — `release` is, and its
premise is that the count is one. -/
theorem counted_decRef {c : CHeap} {handles : List Ref} (hc : Counted c handles) {r : Ref}
    (hhandle : 1 ≤ handles.count r) : Counted (decRef c handles r).1 (decRef c handles r).2 := by
  have hcs : ∀ x, CHeap.count c x = (CHeap.slots c).count x + handles.count x :=
    (counted_iff_slots c handles).mp hc
  have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by rw [hcs r]; omega)
  simp only [decRef]
  rw [counted_iff_slots]
  intro x
  rw [CHeap.slots_adjust]
  by_cases hx : x = r
  · have hcr : CHeap.count c r = (CHeap.slots c).count r + handles.count r := hcs r
    rw [hx, CHeap.count_adjust_self c r (· - 1) hr, dropHandle_count_self]
    omega
  · rw [CHeap.count_adjust_of_ne c r (· - 1) hx, dropHandle_count_of_ne hx, hcs x]

/-- The deallocation with the released handle preserves `Counted`: the released
cell's own count and its one handle go together, and the cells its slots named lose
exactly the occurrences it contributed.

Its premises: the count at `r` is one and the handle list holds a handle on it. -/
theorem counted_dealloc_handle {c : CHeap} {handles : List Ref} (hW : CHeap.WF c)
    (hc : Counted c handles) {r : Ref} (h1 : CHeap.count c r = 1)
    (hhandle : 1 ≤ handles.count r) : Counted (CHeap.dealloc c r) (dropHandle handles r) := by
  have hcs : ∀ x, CHeap.count c x = (CHeap.slots c).count x + handles.count x :=
    (counted_iff_slots c handles).mp hc
  have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by rw [h1]; omega)
  have hsr : (CHeap.slots c).count r = 0 := by
    have := hcs r
    omega
  have hksr : (CHeap.slotsAt c r).count r = 0 := by
    have := CHeap.slotsAt_count_le_slots c r hr r
    omega
  have hhr : handles.count r = 1 := by
    have := hcs r
    omega
  rw [counted_iff_slots]
  intro x
  by_cases hx : x = r
  · rw [hx, CHeap.count_dealloc_self hW r, CHeap.count_slots_dealloc c r hr r, hsr, hksr,
      dropHandle_count_self, hhr]
  · by_cases hxr : x ∈ CHeap.refs c
    · rw [CHeap.count_dealloc_of_ne c r hx hxr hr, CHeap.count_slots_dealloc c r hr x,
        dropHandle_count_of_ne hx]
      have hbound := CHeap.slotsAt_count_le_slots c r hr x
      have := hcs x
      omega
    · rw [CHeap.count_dealloc_not_mem c r hxr, CHeap.count_slots_dealloc c r hr x,
        Counted.slots_count_eq_zero hc hxr, dropHandle_count_of_ne hx,
        Counted.handles_count_eq_zero hc hxr]
      have hbound := CHeap.slotsAt_count_le_slots c r hr x
      omega

/-- The final release preserves the invariant: the deallocation removes one
reference and the cascade removes the cells whose counts it brings to zero. -/
theorem CHeap.wf_release {c : CHeap} {handles : List Ref} {r : Ref} (hW : CHeap.WF c) :
    CHeap.WF (release c handles r).1 := by
  simp only [release]
  exact CHeap.wf_cascade (CHeap.wf_dealloc hW r)

/-- The final release in its own right: the heap it returns lists no cell at the
released reference — the deallocation removed the cell and the cascade removes
cells rather than adding them — and it carries no cell whose count is zero, since
the cascade runs exactly until that holds. -/
theorem release_live_and_freed {c : CHeap} {handles : List Ref} {r : Ref} (hW : CHeap.WF c) :
    CHeap.Live (release c handles r).1 ∧ CHeap.count (release c handles r).1 r = 0 := by
  have hnot : r ∉ CHeap.refs (CHeap.dealloc c r) := by
    rw [CHeap.refs_dealloc]
    exact dropHandle_not_mem_self_of_nodup hW r
  simp only [release]
  exact ⟨CHeap.live_cascade _, CHeap.count_cascade_of_not_mem hnot⟩

/-- The final release preserves `Counted`: the released cell's count and handle go
together, the cells its slots named lose what it contributed, and the cascade frees
exactly the cells whose counts reach zero. -/
theorem counted_release {c : CHeap} {handles : List Ref} (hW : CHeap.WF c) (hc : Counted c handles)
    {r : Ref} (h1 : CHeap.count c r = 1) (hhandle : 1 ≤ handles.count r) :
    Counted (release c handles r).1 (release c handles r).2 := by
  simp only [release]
  exact counted_cascade (CHeap.wf_dealloc hW r) (counted_dealloc_handle hW hc h1 hhandle)

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
old cell keeps its slots and loses a reference.

The destructive branch also does what the write does to the references it
overwrites: the cell's old slots are dropped, and a cell whose count that brings
to zero is freed, which is the cascade. The copying branch drops one handle on the
old cell and leaves every other cell's count standing or raised, so it frees
nothing. -/

/-- The update the lowering performs: when the cell's count is one the write is
destructive — the cell keeps its location and the references its old slots held are
dropped, freeing any cell whose count reaches zero — and otherwise the result is a
fresh cell and the old one loses a reference. -/
def update (c : CHeap) (handles : List Ref) (r : Ref) (ks : List Ref) : CHeap × List Ref :=
  if CHeap.count c r = 1 then
    (CHeap.cascade (CHeap.writeSlots c r ks), handles)
  else
    ((fresh c ks, cellOf ks) :: CHeap.addOccurrences (CHeap.adjust c r (· - 1)) ks,
      fresh c ks :: dropHandle handles r)

/-- The update at a cell whose count is one: the destructive branch. -/
theorem update_of_count_one (c : CHeap) (handles : List Ref) (r : Ref) (ks : List Ref)
    (h : CHeap.count c r = 1) :
    update c handles r ks = (CHeap.cascade (CHeap.writeSlots c r ks), handles) := by
  simp [update, h]

/-- The update at a cell whose count is not one: the copying branch. -/
theorem update_of_count_ne_one (c : CHeap) (handles : List Ref) (r : Ref) (ks : List Ref)
    (h : CHeap.count c r ≠ 1) :
    update c handles r ks =
      ((fresh c ks, cellOf ks) :: CHeap.addOccurrences (CHeap.adjust c r (· - 1)) ks,
        fresh c ks :: dropHandle handles r) := by
  simp [update, h]

/-- The destructive write preserves the invariant: it changes no reference. -/
theorem CHeap.wf_writeSlots {c : CHeap} {r : Ref} {ks : List Ref} (hW : CHeap.WF c) :
    CHeap.WF (CHeap.writeSlots c r ks) := by
  rw [CHeap.WF, CHeap.refs_writeSlots]
  exact hW

/-- The update preserves the invariant, in both branches: the destructive branch
keeps the heap's references and lets the cascade remove some, and the copying
branch's fresh location is beyond every reference the heap lists. -/
theorem CHeap.wf_update {c : CHeap} {handles : List Ref} {r : Ref} {ks : List Ref}
    (hW : CHeap.WF c) : CHeap.WF (update c handles r ks).1 := by
  by_cases h1 : CHeap.count c r = 1
  · rw [update_of_count_one c handles r ks h1]
    exact CHeap.wf_cascade (CHeap.wf_writeSlots hW)
  · rw [update_of_count_ne_one c handles r ks h1, CHeap.WF, CHeap.refs_cons,
      CHeap.refs_addOccurrences, CHeap.refs_adjust]
    exact List.nodup_cons.mpr ⟨fresh_not_mem_refs c ks, hW⟩

/-- The update preserves liveness, in both branches: the destructive branch's
cascade runs exactly until no listed cell carries a count of zero, and the copying
branch's fresh cell has count one, the cells `ks` names have theirs raised, and the
old cell's own count stands at two or more before the one handle the update
releases is taken out. -/
theorem CHeap.live_update {c : CHeap} {handles : List Ref} {r : Ref} {ks : List Ref}
    (h : CHeap.Healthy c) : CHeap.Live (update c handles r ks).1 := by
  obtain ⟨hW, hl⟩ := h
  by_cases h1 : CHeap.count c r = 1
  · rw [update_of_count_one c handles r ks h1]
    exact CHeap.live_cascade _
  · rw [CHeap.live_iff_refs (CHeap.wf_update hW), update_of_count_ne_one c handles r ks h1]
    intro x hx
    rw [CHeap.refs_cons] at hx
    by_cases hfx : x = fresh c ks
    · rw [hfx, CHeap.count_cons_self, cellOf_count]
      omega
    · have hx' : x ∈ CHeap.refs (CHeap.addOccurrences (CHeap.adjust c r (· - 1)) ks) := by
        rcases List.mem_cons.mp hx with heq | hmem
        · exact absurd heq hfx
        · exact hmem
      have hxadj : x ∈ CHeap.refs (CHeap.adjust c r (· - 1)) := by
        have h := hx'
        rwa [CHeap.refs_addOccurrences] at h
      rw [CHeap.count_cons_of_ne (by exact fun hh => hfx hh.symm),
        CHeap.count_addOccurrences_mem _ _ hxadj]
      by_cases hxr : x = r
      · rw [hxr]
        have hmem : r ∈ CHeap.refs c := by
          have h := hxadj
          rw [hxr] at h
          rwa [CHeap.refs_adjust] at h
        rw [CHeap.count_adjust_self c r (· - 1) hmem]
        have := (CHeap.live_iff_refs hW).mp hl r hmem
        omega
      · rw [CHeap.count_adjust_of_ne c r (· - 1) hxr]
        have hmem : x ∈ CHeap.refs c := by
          have h := hxadj
          rwa [CHeap.refs_adjust] at h
        have := (CHeap.live_iff_refs hW).mp hl x hmem
        omega

/-- Under a count of one the write is destructive, and the updated slots are read
back at the same location.

Its premises: the write holds a handle on the cell — which is why no cell's slots
name it, so nothing the write's old slots held stands at the location the write
lands at — and the new slots do not name the cell itself. -/
theorem update_preserves_location_of_exclusive {c : CHeap} {handles : List Ref}
    (hW : CHeap.WF c) (hc : Counted c handles) {r : Ref} {ks : List Ref}
    (h1 : Exclusive (CHeap.presentation c) handles r) (hhandle : 1 ≤ handles.count r)
    (hks : r ∉ ks) :
    (update c handles r ks).1.lookup r = some ks := by
  have hcs : ∀ x, CHeap.count c x = (CHeap.slots c).count x + handles.count x :=
    (counted_iff_slots c handles).mp hc
  have h1' : CHeap.count c r = 1 := (counted_iff_exclusive hc r).mpr h1
  have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by omega)
  have hs0 : (CHeap.slots c).count r = 0 := by
    have := hcs r
    omega
  rw [update_of_count_one c handles r ks h1']
  have hks2 : (CHeap.slotsAt c r).count r = 0 := by
    have := CHeap.slotsAt_count_le_slots c r hr r
    omega
  have hs' : (CHeap.slots (CHeap.writeSlots c r ks)).count r = 0 := by
    rw [CHeap.count_slots_writeSlots c r ks hr r, hs0, hks2, List.count_eq_zero.mpr hks]
  have hp' : 0 < CHeap.count (CHeap.writeSlots c r ks) r := by
    rw [CHeap.count_writeSlots_self c r ks hr]
    omega
  rw [CHeap.lookup_cascade_of_slot_free (CHeap.wf_writeSlots hW) hs' hp',
    CHeap.lookup_writeSlots_self c r ks hr]

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

/-- The destructive branch preserves `Counted`: the write's own counting theorem
covers the slots it replaces, and the cascade covers the cells whose counts reach
zero. -/
theorem counted_update_exclusive {c : CHeap} {handles : List Ref} (hW : CHeap.WF c)
    (hc : Counted c handles) {r : Ref} {ks : List Ref}
    (h1 : Exclusive (CHeap.presentation c) handles r) (hks : r ∉ ks)
    (hself : r ∉ CHeap.slotsAt c r) (hlive : ∀ x ∈ ks, x ∈ CHeap.refs c) :
    Counted (update c handles r ks).1 (update c handles r ks).2 := by
  have h1' : CHeap.count c r = 1 := (counted_iff_exclusive hc r).mpr h1
  have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by omega)
  rw [update_of_count_one c handles r ks h1']
  exact counted_cascade (CHeap.wf_writeSlots hW) (counted_writeSlots hc hr hks hself hlive)

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
then two, so an update below it copies; a decrement of that handle first restores
the count of one, so the update keeps the location. This is the modelled form of
the trap the in-place check caught in its `layout5-checked-unique` case: the check
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

/-- The decrement of the pair's handle: with one handle left the element's count is
one, so it is exclusive again. -/
theorem takeout_dropped_count_one {c : CHeap} {e : Ref} (hc : Counted c [e, e])
    (h0 : (CHeap.presentation c).occurrences e = 0) :
    (decRef c [e, e] e).1.count e = 1 ∧
      Exclusive (CHeap.presentation (decRef c [e, e] e).1) (decRef c [e, e] e).2 e := by
  have h := pair_needs_the_drop (CHeap.presentation c) e h0
  have htwo : CHeap.count c e = 2 := by rw [hc e, h.1]
  have hdec := counted_decRef hc (r := e) (by simp)
  have hcount : CHeap.count (decRef c [e, e] e).1 e = 1 := by
    have hr : e ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by rw [htwo]; omega)
    simp only [decRef]
    rw [CHeap.count_adjust_self c e (· - 1) hr, htwo]
  exact ⟨hcount, (counted_iff_exclusive hdec e).mp hcount⟩

/-- The pair read at the update's decision: with the pair's handle still held the
update below the element copies to a fresh location, and with the handle released
first the same update keeps the location.

The decrement is what the take-out does when it destructures the pair, and it is
what turns the update below it from the copying branch back to the destructive
one. The element's own location survives that write's cascade because no cell's
slots name it: its count is one and the write holds the handle that makes it one. -/
theorem takeout_pair_update_branches {c : CHeap} {e : Ref} {ks : List Ref} (hW : CHeap.WF c)
    (hc : Counted c [e, e]) (h0 : (CHeap.presentation c).occurrences e = 0) (hks : e ∉ ks) :
    (update c [e, e] e ks).1.lookup (fresh c ks) = some ks ∧
      (update (decRef c [e, e] e).1 (decRef c [e, e] e).2 e ks).1.lookup e = some ks := by
  refine ⟨(update_copies_of_shared hc (takeout_pair_count_two hc h0).2 (by simp) hks).1, ?_⟩
  have h1 := (takeout_dropped_count_one hc h0).1
  have he : e ∈ CHeap.refs (decRef c [e, e] e).1 :=
    CHeap.mem_refs_of_count_pos _ (by rw [h1]; omega)
  have hfac : (CHeap.slots (decRef c [e, e] e).1).count e = 0 := by
    simp only [decRef, CHeap.slots_adjust]
    rw [← CHeap.occurrences_presentation]
    exact h0
  rw [update_of_count_one _ _ e ks h1]
  have hslot : (CHeap.slots (CHeap.writeSlots (decRef c [e, e] e).1 e ks)).count e = 0 := by
    rw [CHeap.count_slots_writeSlots _ e ks he, hfac, List.count_eq_zero.mpr hks]
    have hbound := CHeap.slotsAt_count_le_slots (decRef c [e, e] e).1 e he e
    rw [hfac] at hbound
    omega
  have hpos : 0 < CHeap.count (CHeap.writeSlots (decRef c [e, e] e).1 e ks) e := by
    rw [CHeap.count_writeSlots_self _ e ks he]
    omega
  have hlook : (CHeap.cascade ((decRef c [e, e] e).1.writeSlots e ks)).lookup e
      = ((decRef c [e, e] e).1.writeSlots e ks).lookup e :=
    CHeap.lookup_cascade_of_slot_free (c := (decRef c [e, e] e).1.writeSlots e ks) (r := e)
      (CHeap.wf_writeSlots (CHeap.wf_decRef (handles := [e, e]) (r := e) hW)) hslot hpos
  rw [hlook, CHeap.lookup_writeSlots_self _ e ks he]

end RCHeap
end Scidonia.FracPerm.StateVar
