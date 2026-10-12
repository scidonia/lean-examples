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
`refCount = 1`. The facts the model's write test rests on follow from it: one
handle to a root no slot names has count one; a second handle to the same cell
has count two; a second slot naming the same cell has count at least two. A cell
whose count is not one is what this model classifies as an out-of-place cell, and
the model's `Exclusive` test fails at it.

Two readings are **hypotheses**, not theorems:

* that the presentation *is* the live heap — that the cells listed are exactly
  the live cells and no live reference is left out. The presentation reading is
  what makes the counts about a running program; nothing here constructs such a
  presentation from a program, and a presentation that omitted or duplicated a
  cell would still satisfy every theorem below.
* `RuntimeAgrees`: that a model state of one live reference means the count the
  runtime holds passes `RefCount.IsExclusive`. It appears as a hypothesis of the
  theorems that use it and is never proved: no instance of it is constructed in
  this module or in the checks that accompany it, which take it only as a
  hypothesis. `RefCount` is the counter-level vocabulary of the runtime's own
  test, and no bridge from one to the other is derived here.

The counted layer **composes** with the interface's proved detachment. The
state-variable class proves that a primitive observation of a valid state encodes
without a reference to the root it read (`observe_detached`), and
`Scidonia.FracPerm.StateVar.Heap` carries that law through a read of the model's
root (`read_at_detached`). `Value.refs` is the references an encoded value names,
`noRef_iff_refs_count` reads `NoRef` as that list's count being zero, and
`readAt_result_holds_no_handle` is the interface's law at that vocabulary. What
the counted layer then says is `refCount_one_of_detached_issues`: a run whose
every issued read result is detached from the root holds no handle on it but the
runner's own, so the root's count is one; `not_exclusive_of_issued_loc` is the
same shape with an issued result that names the root, whose count is two. The
composition is with a law the interface has already proved — it adds no
detachment fact of its own, and it is still a statement about an issued *value*,
not about a compiled object.

What this module does **not** say: no theorem certifies that a compiled write
updates in place, that a copy happens when it does not, or anything about Lean's
object graph, its allocation, or the compiler's reset/reuse pass. Those are the
correspondence links of `FracPerm_Linearity_Proposal.md` §4 S5, and they stay
outside this module. The `Ref`s here are `Nat` names into a list, not addresses,
and the counts are logical counts of occurrences, not machine words.

This module imports `Scidonia.FracPerm.StateVar.Layout5` for the observation
universe, `Scidonia.FracPerm.StateVar.RefCount` for the runtime's test, and
`Scidonia.FracPerm.StateVar.Heap` for the model's reads, and it changes none of
them. It adds no runtime code: nothing in it runs.
-/
import Scidonia.FracPerm.StateVar.Layout5
import Scidonia.FracPerm.StateVar.RefCount
import Scidonia.FracPerm.StateVar.Heap

namespace Scidonia.FracPerm.StateVar
namespace Footprint

open Scidonia.FracPerm.StateVar.Layout5

/-! ## The presentation and its counts

A reference, the two shapes a node takes, and the count of a reference in a
presentation. The count is layered so that each layer can be reasoned about on
its own: `Node.slots` is what one cell contributes, `Presentation.slots`
concatenates every live cell's contribution, `Presentation.occurrences` counts
one reference among them, and `refCount` adds the handles held outside the
store. -/

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

The type is called a *presentation* rather than a heap because the model's own
heap is `Scidonia.FracPerm.StateVar.Heap`, the single-root `Loc → Option σ` the
counts below are read against; a name of its own keeps the two apart and leaves
`Heap` meaning the model's type alone.

That reading — that the list names exactly the live cells — is a hypothesis of
every count below rather than a proved property: this type is a list, and a list
can name a cell twice or leave a live cell out. -/
abbrev Presentation := List (Ref × Node)

/-- Every reference occurrence in the presentation's slots, in cell order.

The cells are concatenated with `List.flatMap`, the concatenating map of a list,
so the occurrences of the presentation are its cells' occurrences end to end. -/
def Presentation.slots (h : Presentation) : List Ref := h.flatMap (fun c => c.2.slots)

/-- An empty presentation contributes no occurrence. -/
theorem Presentation.slots_nil : Presentation.slots [] = ([] : List Ref) := rfl

/-- A presentation prepends a cell's occurrences to the rest of them. -/
theorem Presentation.slots_cons (c : Ref) (n : Node) (h : Presentation) :
    Presentation.slots ((c, n) :: h) = Node.slots n ++ Presentation.slots h := rfl

/-- Concatenating two presentations concatenates their occurrences. -/
theorem Presentation.slots_append (h₁ h₂ : Presentation) :
    Presentation.slots (h₁ ++ h₂) = Presentation.slots h₁ ++ Presentation.slots h₂ := by
  simp [Presentation.slots, List.flatMap_append]

/-- How many of the presentation's slots name `r`.

This is the store's share of the count: the slots of every live cell, counted
with `List.count`, which is equality of references (`Ref` is `Nat`, whose `BEq`
is lawful). Nothing about the cells themselves is counted — a leaf contributes
nothing and a cell contributes only through its slots. -/
def Presentation.occurrences (h : Presentation) (r : Ref) : Nat := (Presentation.slots h).count r

/-- The modelled reference count of `r`: its occurrences among the live cells'
slots, plus its occurrences among the handles held outside the store.

The handles are the runner's own handle, a caller's binding, a live temporary —
whatever holds a reference to `r` without being a slot of a live cell. The count
is the sum, so the same reference is counted once per occurrence on either side,
and this definition is what makes "the count" a fact about a presentation rather
than a number a program asserts. -/
def refCount (h : Presentation) (handles : List Ref) (r : Ref) : Nat :=
  h.occurrences r + handles.count r

/-- Exclusive ownership, as the count a write tests: exactly one live reference.

The predicate is the modelled test. Whether the runtime's own test agrees with it
is `RuntimeAgrees`, which is a hypothesis and not proved here. -/
def Exclusive (h : Presentation) (handles : List Ref) (r : Ref) : Prop :=
  refCount h handles r = 1

/-! ## Counts of handles

The two ways a handle list moves a count: a handle to `r` itself, and a handle to
something else. These are the add and drop steps the discipline theorem composes,
and the frame lemmas the later theorems rewrite with. -/

/-- A handle to another reference leaves the count alone. -/
theorem refCount_cons_of_ne {x r : Ref} (hx : x ≠ r) (h : Presentation) (handles : List Ref) :
    refCount h (x :: handles) r = refCount h handles r := by
  unfold refCount
  simp only [List.count_cons_of_ne (b := x) (a := r) hx]

/-- A handle to `r` raises its count by one. -/
theorem refCount_cons_self (h : Presentation) (handles : List Ref) (r : Ref) :
    refCount h (r :: handles) r = refCount h handles r + 1 := by
  unfold refCount
  simp only [List.count_cons_self]
  omega

/-! ## One handle to a root no slot names: the count is one

The first fact the discipline rests on, and the one its write's own handle
supplies. -/

/-- With no slot naming `r`, one handle to it is one live reference.

`h.occurrences r = 0` is the store's side — no live cell's slots name `r` — and
the handle list is `[r]` itself, so the count is exactly one. -/
theorem refCount_single_handle (h : Presentation) (r : Ref) (h0 : h.occurrences r = 0) :
    refCount h [r] r = 1 := by
  unfold refCount
  rw [h0]
  simp

/-- The same count stated as exclusivity: one handle to an unnamed root is
exclusive, so the model's write test holds for a write that holds exactly that
handle. -/
theorem exclusive_single_handle (h : Presentation) (r : Ref) (h0 : h.occurrences r = 0) :
    Exclusive h [r] r :=
  refCount_single_handle h r h0

/-- The single-handle count for a caller that holds its handle list as a variable
`handles`: if `handles` is `[r]` and no slot names `r`, then the count of `r` is
one.

The handle list is carried as an equality rather than written out, so a caller
that knows its list only up to `handles = [r]` gets the count without first
rewriting its own term. -/
theorem refCount_of_handles_eq (h : Presentation) (handles : List Ref) (r : Ref)
    (h0 : h.occurrences r = 0) (hh : handles = [r]) : refCount h handles r = 1 := by
  subst hh
  exact refCount_single_handle h r h0

/-- The same, as exclusivity over a handle list known to be `[r]`. -/
theorem exclusive_of_handles_eq (h : Presentation) (handles : List Ref) (r : Ref)
    (h0 : h.occurrences r = 0) (hh : handles = [r]) : Exclusive h handles r :=
  refCount_of_handles_eq h handles r h0 hh

/-! ## The extra reference: the take-out pair is not exclusive

The second fact. Two handles to the same `r` are two live references, so the
count is two and the model's `Exclusive` test fails at the cell they name: this
is the modelled take-out pair, and while the pair is live the model classifies
that cell as out-of-place. -/

/-- Two handles to `r`, and no slot naming it, are two live references.

`refCount h [r, r] r = 2` under `h.occurrences r = 0`: the store contributes
nothing and the pair contributes two. The pair is what a take-out holds while it
has an element out of its array. -/
theorem refCount_pair_of_no_slot (h : Presentation) (r : Ref) (h0 : h.occurrences r = 0) :
    refCount h [r, r] r = 2 := by
  unfold refCount
  rw [h0]
  simp

/-- Two handles to the same reference are never exclusive, whatever the store
names: the two handles alone are two live references, so the count is at least
two and cannot be one.

The hypothesis `h.occurrences r = 0` of the count form is not needed here, which
is why the statement does not carry it. -/
theorem not_exclusive_pair (h : Presentation) (r : Ref) : ¬ Exclusive h [r, r] r := by
  intro hx
  unfold Exclusive refCount at hx
  have hc : ([r, r] : List Ref).count r = 2 := by simp
  rw [hc] at hx
  omega

/-! ## Aliasing in the store: two slots naming one cell

The third fact. A presentation whose slots name `r` twice makes the count two
even with no handle at all, so aliasing is what the store itself can create. -/

/-- Two slot occurrences of `r`, with no handle, are two live references. -/
theorem refCount_of_two_occurrences (h : Presentation) (r : Ref) (h2 : h.occurrences r = 2) :
    refCount h [] r = 2 := by
  unfold refCount
  rw [h2]
  simp

/-- At least two slot occurrences of `r` make the count at least two, against any
handle list: `2 ≤ h.occurrences r` alone rules exclusivity out.

One slot occurrence and one handle suffice as well — `not_exclusive_of_slot_and_handle`
— so this is the part of the aliasing story that needs no outside reference. -/
theorem not_exclusive_of_two_occurrences {h : Presentation} {handles : List Ref} {r : Ref}
    (h2 : 2 ≤ h.occurrences r) : ¬ Exclusive h handles r := by
  intro hx
  unfold Exclusive refCount at hx
  omega

/-- One slot occurrence of `r` and one handle to it are two live references: the
store names `r` and an outside handle names it too, so the count is at least two.

This is the case a chain of cells runs into when a second handle to an interior
node is held: the slot that points at the node and the handle are two names. -/
theorem not_exclusive_of_slot_and_handle {h : Presentation} {handles : List Ref} {r : Ref}
    (hs : 1 ≤ h.occurrences r) (hh : 1 ≤ handles.count r) : ¬ Exclusive h handles r := by
  intro hx
  unfold Exclusive refCount at hx
  omega

/-! ## The references an issued value names

The bridge from the interface's own detachment predicate to a counted list. The
class proves that a primitive read's result encodes without a reference to the
root it read (`observe_detached`); `Value.refs` is the list that detachment is
about, and `noRef_iff_refs_count` reads the predicate as that list's count. -/

/-- The references a value names, in order: `.loc k` names `k`; `some`, `inl`,
`inr` and `pair` descend; every other constructor names none. -/
def Value.refs : Value → List Ref
  | .loc k    => [k]
  | .some v   => Value.refs v
  | .inl v    => Value.refs v
  | .inr v    => Value.refs v
  | .pair x y => Value.refs x ++ Value.refs y
  | _         => []

/-- A value names no root at `ℓ` exactly when `ℓ` occurs nowhere among the
references it names: `NoRef ℓ v ↔ (Value.refs v).count ℓ = 0`. -/
theorem noRef_iff_refs_count (ℓ : Loc) (v : Value) :
    NoRef ℓ v ↔ (Value.refs v).count ℓ = 0 := by
  induction v with
  | loc k =>
      rw [Value.refs, noRef_loc, List.count_eq_zero, List.mem_singleton]
      exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
  | unit => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | nat _ => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | uint _ => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | bool _ => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | none => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | some _ ih => exact ih
  | inl _ ih => exact ih
  | inr _ ih => exact ih
  | pair x y ihx ihy =>
      simp only [Value.refs, noRef_pair, List.count_append]
      rw [ihx, ihy]
      exact Nat.add_eq_zero_iff.symm

/-! ## The handles a list of issued values holds

A run hands out read results one after another, and the handles it holds are the
references those results name, end to end. -/

/-- The handles a list of issued read results holds, in order. -/
def handlesOf (vs : List Value) : List Ref := vs.flatMap Value.refs

/-- The empty list of issued read results holds no handle. -/
theorem handlesOf_nil : handlesOf [] = ([] : List Ref) := rfl

/-- The first issued result's handles come before the rest's. -/
theorem handlesOf_cons (v : Value) (vs : List Value) :
    handlesOf (v :: vs) = Value.refs v ++ handlesOf vs := rfl

/-- Two runs' issued read results are their handles end to end. -/
theorem handlesOf_append (vs ws : List Value) :
    handlesOf (vs ++ ws) = handlesOf vs ++ handlesOf ws := by
  simp [handlesOf, List.flatMap_append]

/-- A run whose every issued read result is detached from `ℓ` holds no handle on
`ℓ`: the count of `ℓ` among the handles is zero.

The detachment is read at each value through `noRef_iff_refs_count` and the
counts are added up, so this is the step that brings the interface's predicate
into the counted layer. -/
theorem handlesOf_count_eq_zero_of_detached {ℓ : Loc} {vs : List Value}
    (h : ∀ v ∈ vs, NoRef ℓ v) : (handlesOf vs).count ℓ = 0 := by
  induction vs with
  | nil => simp [handlesOf]
  | cons v vs ih =>
      rw [handlesOf_cons, List.count_append,
        (noRef_iff_refs_count ℓ v).mp (h v (by simp)),
        ih (fun w hw => h w (by simp [hw]))]

/-! ## The composition: a detached run holds the root's one handle

The two hypotheses the theorem below takes are the two readings the module note
names: that the presentation is the live heap, so no cell's slots name the root,
and that the value list is the read results the run handed out, so none of them
names the root either. What remains of the root's count is the runner's own
handle — the composition with the interface's proved detachment, at the counts
this module defines. -/

/-- A run whose every issued read result is detached from the root has no handle
on the root but the runner's own, so the root's count is one.

This is a statement about the model. The two hypotheses are the two readings the
module note names: `hstore` reads the presentation as the live heap, so no cell's
slots name `r`, and `hdetached` reads the value list as the run's issued read
results, so none of them names `r` — and the interface is what supplies the
second reading, since `read_at_detached` carries its detachment law through a
read. -/
theorem refCount_one_of_detached_issues (p : Presentation) (vs : List Value)
    (r : Ref)
    (hstore : p.occurrences r = 0) (hdetached : ∀ v ∈ vs, NoRef r v) :
    refCount p (r :: handlesOf vs) r = 1 := by
  unfold refCount
  rw [hstore, List.count_cons_self, handlesOf_count_eq_zero_of_detached hdetached]

/-- The countermodel at the same shape: an issued read result that names the root
itself leaves the root's count two, so nothing in that run's handle list is
exclusive there.

The value names the root, which is what detachment forbids, so the handle list is
`[r, r]` — the runner's own handle and the issued result's — and the count is two
rather than one. Detachment is therefore load-bearing: an encoding that puts a
`.loc` where `observe_detached` refuses one, or a raw handle a caller kept, has
the count this statement gives, not the count of
`refCount_one_of_detached_issues`. -/
theorem not_exclusive_of_issued_loc (p : Presentation) (r : Ref)
    (h0 : p.occurrences r = 0) :
    refCount p (r :: handlesOf [Value.loc r]) r = 2 ∧
      ¬ Exclusive p (r :: handlesOf [Value.loc r]) r := by
  have hhandles : r :: handlesOf [Value.loc r] = [r, r] := by
    simp [handlesOf, Value.refs]
  refine ⟨?_, ?_⟩
  · rw [hhandles]
    exact refCount_pair_of_no_slot p r h0
  · intro hx
    rw [hhandles] at hx
    exact not_exclusive_pair p r hx

/-! ## Elementary steps: writing one cell's slots

A write changes one cell's slots. `Presentation.setSlots` is that step, and the
theorems below say what it does to the counts: the changed cell's contribution is
the new slot list's, every other cell's contribution is untouched, and a
presentation that does not list the cell at all is returned unchanged. -/

/-- The presentation with the slots of every cell at `c` replaced by `ks`.

Structural recursion over the cell list: a cell at `c` keeps its reference and
gets `ks` as its slots, and every other cell is kept as it is. Every cell at `c`
is replaced — a presentation that listed `c` twice would have both replaced —
and the cells' order is preserved. -/
def Presentation.setSlots : Presentation → Ref → List Ref → Presentation
  | [], _, _ => []
  | (c', n) :: t, c, ks =>
      if c' = c then (c', Node.cell ks) :: Presentation.setSlots t c ks
      else (c', n) :: Presentation.setSlots t c ks

/-- Writing slots into an empty presentation changes nothing: it lists no cell. -/
theorem Presentation.setSlots_nil (c : Ref) (ks : List Ref) : Presentation.setSlots [] c ks = [] := rfl

/-- The changed cell is the one written: its slots become `ks` and its reference
is kept. -/
theorem Presentation.setSlots_cons_self (n : Node) (t : Presentation) (c : Ref) (ks : List Ref) :
    Presentation.setSlots ((c, n) :: t) c ks = (c, Node.cell ks) :: Presentation.setSlots t c ks := by
  simp [Presentation.setSlots]

/-- A cell at another reference is kept as it is. -/
theorem Presentation.setSlots_cons_of_ne {c c' : Ref} (h : c' ≠ c) (n : Node) (t : Presentation)
    (ks : List Ref) :
    Presentation.setSlots ((c', n) :: t) c ks = (c', n) :: Presentation.setSlots t c ks := by
  simp [Presentation.setSlots, h]

/-- Writing one cell's slots distributes over the parts of a presentation: the
write is on the cell list, so splitting the list splits the write. -/
theorem Presentation.setSlots_append (h₁ h₂ : Presentation) (c : Ref) (ks : List Ref) :
    Presentation.setSlots (h₁ ++ h₂) c ks
      = Presentation.setSlots h₁ c ks ++ Presentation.setSlots h₂ c ks := by
  induction h₁ with
  | nil => simp [Presentation.setSlots]
  | cons e t ih => simp only [List.cons_append, Presentation.setSlots]; split <;> simp [ih]

/-- A presentation that lists no cell at `c` is returned unchanged: writing a
cell's slots cannot touch a cell the presentation does not have.

This is the frame step of a one-cell write, and the reason the theorem below can
speak about "every other cell" without a separate hypothesis for each. -/
theorem Presentation.setSlots_of_absent (h : Presentation) (c : Ref) (ks : List Ref)
    (hc : ∀ e ∈ h, e.1 ≠ c) : Presentation.setSlots h c ks = h := by
  induction h with
  | nil => simp [Presentation.setSlots]
  | cons e t ih =>
    rw [Presentation.setSlots_cons_of_ne (hc e (by simp)) e.2 t ks,
      ih (fun e' he' => hc e' (by simp [he']))]

/-- **What a one-cell write does to the counts.** With the presentation split as
`h₁ ++ (c, n) :: h₂` — `h₁` and `h₂` naming no cell at `c`, so `c` names exactly
the one cell being written — rewriting that cell's slots to `ks` moves the count
of `r` by exactly the changed cell's contribution:

`(setSlots …).occurrences r = ks.count r + (slots (h₁ ++ h₂)).count r`.

The right-hand side is the two halves of the statement: the first term is the
changed cell's new contribution, the second is every other cell's contribution,
unchanged. -/
theorem Presentation.setSlots_occurrences (h₁ h₂ : Presentation) (n : Node) (c : Ref) (ks : List Ref)
    (r : Ref) (h₁c : ∀ e ∈ h₁, e.1 ≠ c) (h₂c : ∀ e ∈ h₂, e.1 ≠ c) :
    (Presentation.setSlots (h₁ ++ (c, n) :: h₂) c ks).occurrences r
      = ks.count r + (Presentation.slots (h₁ ++ h₂)).count r := by
  rw [Presentation.setSlots_append, Presentation.setSlots_of_absent h₁ c ks h₁c,
    Presentation.setSlots_cons_self, Presentation.setSlots_of_absent h₂ c ks h₂c]
  simp [Presentation.occurrences, Presentation.slots_cons, Presentation.slots_append,
    List.count_append, Node.slots_cell]
  omega

/-- **The discipline theorem.** With no slot naming `r`, the pair of handles is
two live references and the single handle is one: `refCount h [r, r] r = 2` and
`refCount h [r] r = 1`, together.

At one presentation these are the two sides of the model's write test: the pair's
count of two is a cell the model classifies as out-of-place, where `Exclusive`
fails, and the single handle's count of one is a cell where it holds. The pair's
extra reference — the one it holds while an element is out of the array — is what
has to be dropped before the cell counts one again. -/
theorem pair_needs_the_drop (h : Presentation) (r : Ref) (h0 : h.occurrences r = 0) :
    refCount h [r, r] r = 2 ∧ refCount h [r] r = 1 :=
  ⟨refCount_pair_of_no_slot h r h0, refCount_single_handle h r h0⟩

/-! ## The runtime link, named

The runtime's own test is `RefCount.IsExclusive` on the `Int32` count the object
carries. Relating the modelled count to it is a correspondence the model does not
prove, so it is stated as a hypothesis of the theorems that need it — here rather
than silently in a paper step — and no instance of it is constructed in this
module. -/

/-- The runtime agreement hypothesis: if the model says one live reference then
the count the runtime holds passes `lean_is_exclusive`. Nothing here proves it;
it is the link from this model to the runtime, and it is stated rather than
assumed silently. -/
def RuntimeAgrees (h : Presentation) (handles : List Ref) (r : Ref) (rc : Int32) : Prop :=
  Exclusive h handles r → RefCount.IsExclusive rc

/-- Under the runtime link, a model state that is exclusive gives a runtime count
that passes the runtime's test: the hypothesis `RuntimeAgrees` at the state a
write holds, with the conclusion at the counter `rc` the object carries.

The theorem is an implication through the link and proves nothing about either
side alone: what it carries is the hypothesis, from the model's `Exclusive` test
to the runtime's predicate at the counter `rc`. -/
theorem runtime_agrees_exclusive (h : Presentation) (handles : List Ref) (r : Ref) (rc : Int32)
    (hx : Exclusive h handles r) (hag : RuntimeAgrees h handles r rc) :
    RefCount.IsExclusive rc :=
  hag hx

/-- The link has teeth in the other direction: a runtime count that does *not*
pass the runtime's test rules out exclusivity in the model, so an aliased
presentation cannot be offered to a runtime whose count says otherwise while the
link holds.

The contradiction is between the two premises through `RuntimeAgrees`; it is not a
theorem that the pair of handles *makes* a runtime count two. -/
theorem runtime_not_exclusive_excludes_model (h : Presentation) (handles : List Ref) (r : Ref) (rc : Int32)
    (hag : RuntimeAgrees h handles r rc) (hrc : ¬ RefCount.IsExclusive rc) :
    ¬ Exclusive h handles r :=
  fun hx => hrc (runtime_agrees_exclusive h handles r rc hx hag)

/-! ## The interface's detachment, read at the counted layer

The composition with what the interface already proves, stated on its own. The
class's `observe_detached` says a primitive observation of a valid state encodes
without a reference to the root it read, and `Scidonia.FracPerm.StateVar.Heap`
carries that law through a read of the model's root as `read_at_detached`. Read
through `noRef_iff_refs_count`, that law is a statement about the references the
returned value names, which is the layer the counts live at; it is what discharges
the detachment hypothesis of `refCount_one_of_detached_issues` for a run whose
results came from the model's reads, and it adds no detachment fact of its own. -/

/-- A read of the model's root hands back a value that holds no handle on it:
the interface's own detachment law (`observe_detached`, carried through
`ReadAt` by `read_at_detached`) read at the counted layer.

This is the composition, not a new detachment fact: the work is the interface's,
and all this theorem does is read it as the count of `ℓ` among the references the
value names being zero. -/
theorem readAt_result_holds_no_handle {σ Init ReadOp WriteOp : Type}
    [inst : LawfulStateVar σ Init ReadOp WriteOp] {ℓ : Loc} {o : ReadOp}
    {h h' : Scidonia.FracPerm.StateVar.Heap σ} {v : inst.Result o}
    (hr : ReadAt inst ℓ o h h' v) : (Value.refs (inst.encodeRead o v)).count ℓ = 0 :=
  (noRef_iff_refs_count ℓ (inst.encodeRead o v)).mp (read_at_detached (inst := inst) hr)

end Footprint
end Scidonia.FracPerm.StateVar
