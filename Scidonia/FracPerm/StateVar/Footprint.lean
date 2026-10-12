/-
A presentation of the heap whose reference count is defined from aliasing.

`Scidonia.FracPerm.StateVar.Heap` models a single root cell as `Loc → Option σ`
with an opaque state `σ`. It has no vocabulary in which two handles, or two
slots, can name the same object, so it cannot say what a reference count is. This
module adds that vocabulary. A *presentation* of the heap lists the live cells,
each of which is either an observation leaf of the closed universe `ObsDesc` /
`ObsEl` — it names no further reference — or a cell whose *slots* are references
to further cells. A reference is counted once per occurrence, so the count of a
cell is how many slot occurrences, plus how many handles held outside the store,
name it; exclusivity is that count being one.

The count is a **definition** here, not an assumption. `refCount` is defined over
a presentation and a list of outside handles, and `Exclusive` is the equation
`refCount = 1`. The facts the write discipline rests on follow from it: one
handle to a root no slot names has count one; a second handle to the same cell
has count two; a second slot naming the same cell has count at least two. The
out-of-place cases are exactly the cells whose count is not one.

Two readings are **hypotheses**, not theorems:

* that the presentation *is* the live heap — that the cells listed are exactly
  the live cells and no live reference is left out. The presentation reading is
  what makes the counts about a running program; nothing here constructs such a
  presentation from a program, and a presentation that omitted or duplicated a
  cell would still satisfy every theorem below.
* `RuntimeAgrees`: that a model state of one live reference means the count the
  runtime holds passes `RefCount.IsExclusive`. It appears as a hypothesis of the
  theorems that use it and is never proved; `RefCount` is the counter-level
  vocabulary of the runtime's own test, and no bridge from one to the other is
  derived here.

What this module does **not** say: no theorem certifies that a compiled write
updates in place, that a copy happens when it does not, or anything about Lean's
object graph, its allocation, or the compiler's reset/reuse pass. Those are the
correspondence links of `FracPerm_Linearity_Proposal.md` §4 S5, and they stay
outside this module. The `Ref`s here are `Nat` names into a list, not addresses,
and the counts are logical counts of occurrences, not machine words.

This module imports `Scidonia.FracPerm.StateVar.Layout5` for the observation
universe and `Scidonia.FracPerm.StateVar.RefCount` for the runtime's test, and it
changes neither. It adds no runtime code: nothing in it runs.
-/
import Scidonia.FracPerm.StateVar.Layout5
import Scidonia.FracPerm.StateVar.RefCount

namespace Scidonia.FracPerm.StateVar
namespace Footprint

open Scidonia.FracPerm.StateVar.Layout5

/-! ## The presentation and its counts

A reference, the two shapes a node takes, and the count of a reference in a
presentation. The count is layered so that each layer can be reasoned about on
its own: `Node.slots` is what one cell contributes, `Heap.slots` concatenates
every live cell's contribution, `Heap.occurrences` counts one reference among
them, and `refCount` adds the handles held outside the store. -/

/-- A logical reference: the name of a cell in a presentation.

A presentation is a list, so a reference is a name, not an address; two
presentations never share one, and nothing here says where a cell lives. -/
abbrev Ref := Nat

/-- A node of the presented heap: an observation leaf, which names no further
reference, or a cell whose slots are references to further cells.

The leaf case carries an element of the closed observation universe `ObsEl o`,
so a leaf is immutable data — a unit, a natural, a word, a boolean, or a
sum/option/pair built from them — and it names no cell. The cell case carries
the references its slots hold, and a reference may occur more than once, which is
how aliasing is written down. -/
inductive Node where
  /-- An observation leaf: immutable data of the closed universe, naming no
  further reference. -/
  | leaf (o : ObsDesc) (x : ObsEl o)
  /-- A cell: the references its slots hold, in order, repetitions included. -/
  | cell (slots : List Ref)

/-- The reference occurrences one node contributes to the presentation: a leaf
contributes none, a cell contributes its slot list.

Repetitions are kept, so a slot list `[a, a]` contributes `a` twice. -/
def Node.slots : Node → List Ref
  | .leaf _ _ => []
  | .cell ks => ks

/-- A cell contributes nothing. -/
theorem Node.slots_leaf (o : ObsDesc) (x : ObsEl o) : Node.slots (.leaf o x) = [] := rfl

/-- A cell contributes exactly its slot list. -/
theorem Node.slots_cell (ks : List Ref) : Node.slots (.cell ks) = ks := rfl

/-- A presentation of the heap: the live cells, each with its node. A
presentation lists *exactly* the live cells; it is not a store with garbage.

That reading is a hypothesis of every count below rather than a proved property:
this type is a list, and a list can name a cell twice or leave a live cell out. -/
abbrev Heap := List (Ref × Node)

/-- Every reference occurrence in the presentation's slots, in cell order.

The cells are concatenated with `List.flatMap`, the concatenating map of a list,
so the occurrences of the presentation are its cells' occurrences end to end. -/
def Heap.slots (h : Heap) : List Ref := h.flatMap (fun c => c.2.slots)

/-- An empty presentation contributes no occurrence. -/
theorem Heap.slots_nil : Heap.slots [] = ([] : List Ref) := rfl

/-- A presentation prepends a cell's occurrences to the rest of them. -/
theorem Heap.slots_cons (c : Ref) (n : Node) (h : Heap) :
    Heap.slots ((c, n) :: h) = Node.slots n ++ Heap.slots h := rfl

/-- Concatenating two presentations concatenates their occurrences. -/
theorem Heap.slots_append (h₁ h₂ : Heap) :
    Heap.slots (h₁ ++ h₂) = Heap.slots h₁ ++ Heap.slots h₂ := by
  simp [Heap.slots, List.flatMap_append]

/-- How many of the presentation's slots name `r`.

This is the store's share of the count: the slots of every live cell, counted
with `List.count`, which is equality of references (`Ref` is `Nat`, whose `BEq`
is lawful). Nothing about the cells themselves is counted — a leaf contributes
nothing and a cell contributes only through its slots. -/
def Heap.occurrences (h : Heap) (r : Ref) : Nat := (Heap.slots h).count r

/-- The modelled reference count of `r`: its occurrences among the live cells'
slots, plus its occurrences among the handles held outside the store.

The handles are the runner's own handle, a caller's binding, a live temporary —
whatever holds a reference to `r` without being a slot of a live cell. The count
is the sum, so the same reference is counted once per occurrence on either side,
and this definition is what makes "the count" a fact about a presentation rather
than a number a program asserts. -/
def refCount (h : Heap) (handles : List Ref) (r : Ref) : Nat :=
  h.occurrences r + handles.count r

/-- Exclusive ownership, as the count a write tests: exactly one live reference.

The predicate is the modelled test. Whether the runtime's own test agrees with it
is `RuntimeAgrees`, which is a hypothesis and not proved here. -/
def Exclusive (h : Heap) (handles : List Ref) (r : Ref) : Prop :=
  refCount h handles r = 1

/-! ## Counts of handles

The two ways a handle list moves a count: a handle to `r` itself, and a handle to
something else. These are the add and drop steps the discipline theorem composes,
and the frame lemmas the later theorems rewrite with. -/

/-- A handle to another reference leaves the count alone. -/
theorem refCount_cons_of_ne {x r : Ref} (hx : x ≠ r) (h : Heap) (handles : List Ref) :
    refCount h (x :: handles) r = refCount h handles r := by
  unfold refCount
  simp only [List.count_cons_of_ne (b := x) (a := r) hx]

/-- A handle to `r` raises its count by one. -/
theorem refCount_cons_self (h : Heap) (handles : List Ref) (r : Ref) :
    refCount h (r :: handles) r = refCount h handles r + 1 := by
  unfold refCount
  simp only [List.count_cons_self]
  omega

/-! ## One handle to a root no slot names: the count is one

The first fact the discipline rests on, and the one its write's own handle
supplies. -/

/-- With no slot naming `r`, one handle to it is one live reference.

`h.occurrences r = 0` is the store's side — no live cell's slots name `r` — and
the handle list is `[r]` itself, so the count is exactly one. This says nothing
about whether a compiled write would keep the object single-owner. -/
theorem refCount_single_handle (h : Heap) (r : Ref) (h0 : h.occurrences r = 0) :
    refCount h [r] r = 1 := by
  unfold refCount
  rw [h0]
  simp

/-- The same count stated as exclusivity: one handle to an unnamed root is
exclusive, so a write holding exactly that handle tests true. -/
theorem exclusive_single_handle (h : Heap) (r : Ref) (h0 : h.occurrences r = 0) :
    Exclusive h [r] r :=
  refCount_single_handle h r h0

/-- The single-handle count for a caller that holds its handle list as a variable
`handles`: if `handles` is `[r]` and no slot names `r`, then the count of `r` is
one.

The handle list is carried as an equality rather than written out, so a caller
that knows its list only up to `handles = [r]` gets the count without first
rewriting its own term. -/
theorem refCount_of_handles_eq (h : Heap) (handles : List Ref) (r : Ref)
    (h0 : h.occurrences r = 0) (hh : handles = [r]) : refCount h handles r = 1 := by
  subst hh
  exact refCount_single_handle h r h0

/-- The same, as exclusivity over a handle list known to be `[r]`. -/
theorem exclusive_of_handles_eq (h : Heap) (handles : List Ref) (r : Ref)
    (h0 : h.occurrences r = 0) (hh : handles = [r]) : Exclusive h handles r :=
  refCount_of_handles_eq h handles r h0 hh

/-! ## The extra reference: the take-out pair is not exclusive

The second fact. Two handles to the same `r` are two live references, so the
count is two and no write may store in place: this is the modelled take-out pair,
and while the pair is live a write below the element would copy. -/

/-- Two handles to `r`, and no slot naming it, are two live references.

`refCount h [r, r] r = 2` under `h.occurrences r = 0`: the store contributes
nothing and the pair contributes two. The pair is what a take-out holds while it
has an element out of its array. -/
theorem refCount_pair_of_no_slot (h : Heap) (r : Ref) (h0 : h.occurrences r = 0) :
    refCount h [r, r] r = 2 := by
  unfold refCount
  rw [h0]
  simp

/-- Two handles to the same reference are never exclusive, whatever the store
names: the two handles alone are two live references, so the count is at least
two and cannot be one.

The hypothesis `h.occurrences r = 0` of the count form is not needed here, which
is why the statement does not carry it. -/
theorem not_exclusive_pair (h : Heap) (r : Ref) : ¬ Exclusive h [r, r] r := by
  intro hx
  unfold Exclusive refCount at hx
  have hc : ([r, r] : List Ref).count r = 2 := by simp
  rw [hc] at hx
  omega

/-! ## Aliasing in the store: two slots naming one cell

The third fact. A presentation whose slots name `r` twice makes the count two
even with no handle at all, so aliasing is what the store itself can create. -/

/-- Two slot occurrences of `r`, with no handle, are two live references. -/
theorem refCount_of_two_occurrences (h : Heap) (r : Ref) (h2 : h.occurrences r = 2) :
    refCount h [] r = 2 := by
  unfold refCount
  rw [h2]
  simp

/-- At least two slot occurrences of `r` make the count at least two, against any
handle list: `2 ≤ h.occurrences r` alone rules exclusivity out.

One slot occurrence and one handle suffice as well — `not_exclusive_of_slot_and_handle`
— so this is the part of the aliasing story that needs no outside reference. -/
theorem not_exclusive_of_two_occurrences {h : Heap} {handles : List Ref} {r : Ref}
    (h2 : 2 ≤ h.occurrences r) : ¬ Exclusive h handles r := by
  intro hx
  unfold Exclusive refCount at hx
  omega

/-- One slot occurrence of `r` and one handle to it are two live references: the
store names `r` and an outside handle names it too, so the count is at least two.

This is the case a chain of cells runs into when a second handle to an interior
node is held: the slot that points at the node and the handle are two names. -/
theorem not_exclusive_of_slot_and_handle {h : Heap} {handles : List Ref} {r : Ref}
    (hs : 1 ≤ h.occurrences r) (hh : 1 ≤ handles.count r) : ¬ Exclusive h handles r := by
  intro hx
  unfold Exclusive refCount at hx
  omega

/-! ## Elementary steps: writing one cell's slots

A write changes one cell's slots. `Heap.setSlots` is that step, and the theorems
below say what it does to the counts: the changed cell's contribution is the new
slot list's, every other cell's contribution is untouched, and a presentation
that does not list the cell at all is returned unchanged. -/

/-- The presentation with the slots of every cell at `c` replaced by `ks`.

Structural recursion over the cell list: a cell at `c` keeps its reference and
gets `ks` as its slots, and every other cell is kept as it is. Every cell at `c`
is replaced — a presentation that listed `c` twice would have both replaced —
and the cells' order is preserved. -/
def Heap.setSlots : Heap → Ref → List Ref → Heap
  | [], _, _ => []
  | (c', n) :: t, c, ks =>
      if c' = c then (c', Node.cell ks) :: Heap.setSlots t c ks
      else (c', n) :: Heap.setSlots t c ks

/-- Writing slots into an empty presentation changes nothing: it lists no cell. -/
theorem Heap.setSlots_nil (c : Ref) (ks : List Ref) : Heap.setSlots [] c ks = [] := rfl

/-- The changed cell is the one written: its slots become `ks` and its reference
is kept. -/
theorem Heap.setSlots_cons_self (n : Node) (t : Heap) (c : Ref) (ks : List Ref) :
    Heap.setSlots ((c, n) :: t) c ks = (c, Node.cell ks) :: Heap.setSlots t c ks := by
  simp [Heap.setSlots]

/-- A cell at another reference is kept as it is. -/
theorem Heap.setSlots_cons_of_ne {c c' : Ref} (h : c' ≠ c) (n : Node) (t : Heap)
    (ks : List Ref) :
    Heap.setSlots ((c', n) :: t) c ks = (c', n) :: Heap.setSlots t c ks := by
  simp [Heap.setSlots, h]

/-- Writing one cell's slots distributes over the parts of a presentation: the
write is on the cell list, so splitting the list splits the write. -/
theorem Heap.setSlots_append (h₁ h₂ : Heap) (c : Ref) (ks : List Ref) :
    Heap.setSlots (h₁ ++ h₂) c ks = Heap.setSlots h₁ c ks ++ Heap.setSlots h₂ c ks := by
  induction h₁ with
  | nil => simp [Heap.setSlots]
  | cons e t ih => simp only [List.cons_append, Heap.setSlots]; split <;> simp [ih]

/-- A presentation that lists no cell at `c` is returned unchanged: writing a
cell's slots cannot touch a cell the presentation does not have.

This is the frame step of a one-cell write, and the reason the theorem below can
speak about "every other cell" without a separate hypothesis for each. -/
theorem Heap.setSlots_of_absent (h : Heap) (c : Ref) (ks : List Ref)
    (hc : ∀ e ∈ h, e.1 ≠ c) : Heap.setSlots h c ks = h := by
  induction h with
  | nil => simp [Heap.setSlots]
  | cons e t ih =>
    rw [Heap.setSlots_cons_of_ne (hc e (by simp)) e.2 t ks,
      ih (fun e' he' => hc e' (by simp [he']))]

/-- **What a one-cell write does to the counts.** With the presentation split as
`h₁ ++ (c, n) :: h₂` — `h₁` and `h₂` naming no cell at `c`, so `c` names exactly
the one cell being written — rewriting that cell's slots to `ks` moves the count
of `r` by exactly the changed cell's contribution:

`(setSlots …).occurrences r = ks.count r + (slots (h₁ ++ h₂)).count r`.

The right-hand side is the two halves of the statement: the first term is the
changed cell's new contribution, the second is every other cell's contribution,
unchanged. Nothing here says that the write happens in place; it says which
counts the presentation has afterwards. -/
theorem Heap.setSlots_occurrences (h₁ h₂ : Heap) (n : Node) (c : Ref) (ks : List Ref)
    (r : Ref) (h₁c : ∀ e ∈ h₁, e.1 ≠ c) (h₂c : ∀ e ∈ h₂, e.1 ≠ c) :
    (Heap.setSlots (h₁ ++ (c, n) :: h₂) c ks).occurrences r
      = ks.count r + (Heap.slots (h₁ ++ h₂)).count r := by
  rw [Heap.setSlots_append, Heap.setSlots_of_absent h₁ c ks h₁c,
    Heap.setSlots_cons_self, Heap.setSlots_of_absent h₂ c ks h₂c]
  simp [Heap.occurrences, Heap.slots_cons, Heap.slots_append, List.count_append, Node.slots_cell]
  omega

/-- **The discipline theorem.** With no slot naming `r`, the pair of handles is
two live references and the single handle is one: `refCount h [r, r] r = 2` and
`refCount h [r] r = 1`, together.

This is the out-of-place case and the case a write admits, at the same
presentation: a write that meets the pair must copy, and the pair's extra
reference — the one it took out — has to be dropped before the same cell is
exclusive again. -/
theorem pair_needs_the_drop (h : Heap) (r : Ref) (h0 : h.occurrences r = 0) :
    refCount h [r, r] r = 2 ∧ refCount h [r] r = 1 :=
  ⟨refCount_pair_of_no_slot h r h0, refCount_single_handle h r h0⟩

/-! ## The runtime link, named

The runtime's own test is `RefCount.IsExclusive` on the `Int32` count the object
carries. Relating the modelled count to it is a correspondence the model does not
prove, so it is stated as a hypothesis of the theorems that need it — here rather
than silently in a paper step. -/

/-- The runtime agreement hypothesis: if the model says one live reference then
the count the runtime holds passes `lean_is_exclusive`. Nothing here proves it;
it is the link from this model to the runtime, and it is stated rather than
assumed silently. -/
def RuntimeAgrees (h : Heap) (handles : List Ref) (r : Ref) (rc : Int32) : Prop :=
  Exclusive h handles r → RefCount.IsExclusive rc

/-- Under the runtime link, a model state that is exclusive gives a runtime count
that passes the runtime's test: the hypothesis `RuntimeAgrees` at the state a
write holds, with the conclusion at the counter `rc` the object carries.

The theorem is an implication through the link and proves nothing about either
side alone; in particular it does not show that a compiled object's count is the
modelled count. -/
theorem runtime_agrees_exclusive (h : Heap) (handles : List Ref) (r : Ref) (rc : Int32)
    (hx : Exclusive h handles r) (hag : RuntimeAgrees h handles r rc) :
    RefCount.IsExclusive rc :=
  hag hx

/-- The link has teeth in the other direction: a runtime count that does *not*
pass the runtime's test rules out exclusivity in the model, so an aliased
presentation cannot be offered to a runtime whose count says otherwise while the
link holds.

The contradiction is between the two premises through `RuntimeAgrees`; it is not a
theorem that the pair of handles *makes* a runtime count two. -/
theorem runtime_not_exclusive_excludes_model (h : Heap) (handles : List Ref) (r : Ref) (rc : Int32)
    (hag : RuntimeAgrees h handles r rc) (hrc : ¬ RefCount.IsExclusive rc) :
    ¬ Exclusive h handles r :=
  fun hx => hrc (runtime_agrees_exclusive h handles r rc hx hag)

end Footprint
end Scidonia.FracPerm.StateVar
