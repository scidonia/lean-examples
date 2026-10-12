/-
A run of the counted heap: the steps a program performs, and the write's schema,
as an induction over the step sequence.

`Scidonia.FracPerm.StateVar.RCHeap` proves the *per-step* facts about one update:
at a count of one the write is destructive and the cell keeps its location, and
otherwise the updated slots land at a fresh one. It says nothing about a program:
a run is a sequence of steps, and "every write in an accepted program is
destructive" is an induction over that sequence, which needs the schema the
executor performs at a write — the array steps that take each element out and put
it back on the way to the addressed cell — as an object the induction can follow.

This module supplies that: a path, the schema's write at a path, a program as a
list of steps, the predicate a run starts in and the semantics preserves, and the
induction that gives the per-run statement. The discipline the per-run statement
rests on is the schema's own shape: the take-out's handle is dropped *before* the
focus check, so the cell the write lands at is held once when the write runs.

## What is proved

* the schema, defined rather than asserted: `writeStep` walks a path, and at each
  array step it checks the cell at hand (its `exclusive?`), takes the element out —
  the occurrence leaves the cell's slots and the caller's handle on the extracted
  reference appears — destructures the take-out's pair, drops the pair's handle
  *before* the focus check, checks the extracted element on its own, recurses into
  it, and puts it back at the index the take-out emptied and releases the handle;
  at the end of the path it applies the leaf update, `RCHeap.update`, to the
  addressed cell's slots. Each check is a `Bool` the definition branches on, and a
  step a check turns away is `none`: a run is the sequence of the steps that ran.
  The routing is the same recursion: `resolve` reads the index the schema reads at
  the cell the schema holds, so a path resolves where the recursion follows it.
* the acceptance invariant `Accept`: the heap is healthy (`CHeap.WF` and
  `CHeap.Live`), it is `Counted` at the run's handle list, and that handle list is
  the runner's own handle on the session's root followed by the references the
  run's issued read results hold — and none of those results names a reference,
  since a read issues the encoded observation the sealed surface's read returns.
  So the runner holds the root's handle once, and no other handle names a session
  cell.
* the per-step statements: `writeStep_spec` carries the schema's own facts — the
  handle list is what it was, the heap stays healthy and counted, the addressed
  cell's only name is the handle the write holds, and the written slots are read
  back at the address — and `writeStep_lands` states them at an accepted
  configuration: the leaf update runs at a cell of count one, `counted_iff_exclusive`
  reads the check that made it one as the count the update branches on, so it takes
  the destructive branch by `update_preserves_location_of_exclusive` and the
  addressed cell keeps its location.
* the per-run statement `every_write_step_keeps_its_address`: by induction over
  the step sequence, every write step of the execution of an accepted program is
  destructive at the address it writes and leaves that address unchanged — the
  heap the step leaves reads the written slots back where the path's address was.
* the countermodel `pair_handle_held_copies` beside its affirmative control
  `pair_handle_dropped_keeps`: the same heap, the same path and the same write
  with the take-out's handle still held (the schema's drop removed) updates at a
  cell of count two and therefore copies to a fresh location, which is the shape
  the in-place check's `layout5-checked-unique` case failed on before the pair was
  destructured.

## What is modelled

A program is the *step sequence* read off the executor: the sealed surface's
`set` is the write step at a path, and a read phase's reads are the read steps.
The typing argument that a client cannot name the state is the sealed surface's —
a structural argument about what a type's operations are — and it is not modelled
here; what is modelled is the sequence of steps a run performs.

A path is a list of slot indices, and a reference is a name in a list, not a
machine address; the counts are the runtime's counts modelled, as in `RCHeap`, and
the model's count of one is the test the runtime's `lean_is_exclusive` makes. The
take-out's pair is modelled as it is measured: taking the element out transfers
the occurrence into the caller's handle and the pair holds a second one, so the
extracted element's count is two until the pair is destructured, and this module's
drop is that destructuring. What the runtime puts in the emptied slot — the
layout's placeholder — is not modelled; the occurrence leaves the slot list, and
the put-back reinserts it where it was, which is what the schema's `plugAt` does.
The top-level bounds test the public `setLeaf` adds is not modelled either: the
schema's write is defined at a path that addresses a cell, and a path that does
not is a step the model does not run. A write's operand is a slot list, which
generalises the leaf write's observation, whose references are none; the model
requires of that operand what the counted heap requires — that the slots it names
are live cells and that it does not name the cell it writes — and the put-back
carries the same requirement of the cell it writes.

## What is trusted, and what is outside

Two links to a compiled run are trusted rather than built here:

* that Lean's compiler lowers this repository's `setLeaf` and the sealed surface's
  `set` into the schema modelled here — the array check, the take-out, the focus
  check after the pair's drop, the recursion and the put-back — which
  `ScidoniaTest/IRShape.lean` checks by reading the post-reference-counting IR of
  those declarations.
* that the array-write decision itself is `lean_is_exclusive` inside
  `lean_array_uset` and `lean_ensure_exclusive_array` in the runtime header, and
  not a branch of the emitted IR.

No theorem here says that a compiled write mutates an object: the theorem is about
this model, in which the write at a cell of count one is the destructive branch of
`RCHeap.update` and the location is a name in a list. Nothing here allocates,
frees or reclaims memory, and the run-time evidence for copy-or-mutate stays in
the in-place check of `FracPerm`.

This module imports `Scidonia.FracPerm.StateVar.RCHeap` and changes nothing it
exports. It adds no runtime code: nothing in it runs.
-/
import Scidonia.FracPerm.StateVar.RCHeap

namespace Scidonia.FracPerm.StateVar
namespace Run

open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap

/-! ## Paths and their indices

A path is the list of slot indices a write follows: a cell's slot at an index is a
reference, and the path's next index resolves through that reference's own slots.
The schema walks a path by taking each element out of its array and putting it
back, so the slot list a level reads is the one the take-outs above have made,
and the two list operations below are the two moves: the occurrence leaving the
slot list, and the element going back where it came from. -/

/-- A path: the slot indices a write follows through the heap's cells. -/
abbrev Path := List Nat

/-- The slot list with the element at `i` removed: the element is gone and the
elements after it move up one place. A list shorter than the index is returned
unchanged. -/
def eraseAt : List Ref → Nat → List Ref
  | [], _ => []
  | _ :: t, 0 => t
  | y :: t, n + 1 => y :: eraseAt t n

/-- The slot list with `x` put back at `i`: at an index the erased list left short
this is the element's return to where it came from, and past the end it appends. -/
def putAt : List Ref → Nat → Ref → List Ref
  | [], _, x => [x]
  | y :: t, 0, x => x :: y :: t
  | y :: t, n + 1, x => y :: putAt t n x

/-- Erasing an empty list's element leaves the empty list. -/
@[simp] theorem eraseAt_nil (i : Nat) : eraseAt ([] : List Ref) i = [] := by
  cases i <;> rfl

/-- Erasing the head removes it. -/
@[simp] theorem eraseAt_zero (y : Ref) (t : List Ref) : eraseAt (y :: t) 0 = t := rfl

/-- Erasing past the head keeps it and erases from the tail. -/
@[simp] theorem eraseAt_succ (y : Ref) (t : List Ref) (n : Nat) :
    eraseAt (y :: t) (n + 1) = y :: eraseAt t n := rfl

/-- Putting an element back at the head of an empty list gives the one-element
list. -/
@[simp] theorem putAt_nil (i : Nat) (x : Ref) : putAt ([] : List Ref) i x = [x] := by
  cases i <;> rfl

/-- Putting an element back at the head precedes the head. -/
@[simp] theorem putAt_zero (y : Ref) (t : List Ref) (x : Ref) :
    putAt (y :: t) 0 x = x :: y :: t := rfl

/-- Putting an element back past the head keeps the head and puts it back in the
tail. -/
@[simp] theorem putAt_succ (y : Ref) (t : List Ref) (n : Nat) (x : Ref) :
    putAt (y :: t) (n + 1) x = y :: putAt t n x := rfl

/-- The element a take-out removed goes back where it came from: putting it back
at the index it was erased from replaces that index's element. -/
theorem putAt_eraseAt (l : List Ref) (i : Nat) (x : Ref) (h : i < l.length) :
    putAt (eraseAt l i) i x = l.take i ++ x :: l.drop (i + 1) := by
  induction l generalizing i with
  | nil => simp at h
  | cons y t ih =>
      cases i with
      | zero => cases t with
                | nil => rfl
                | cons z s => rfl
      | succ n =>
          simp only [eraseAt_succ, putAt_succ, List.length_cons, Nat.succ_lt_succ_iff] at h ⊢
          rw [ih n h]
          simp [List.take_succ_cons, List.drop_succ_cons]

/-- An element an erased list holds is one the list held. -/
theorem mem_eraseAt {x : Ref} {l : List Ref} {i : Nat} (h : x ∈ eraseAt l i) : x ∈ l := by
  induction l generalizing i with
  | nil => simp at h
  | cons y t ih =>
      cases i with
      | zero => simp at h; exact List.mem_cons_of_mem y h
      | succ n =>
          simp only [eraseAt_succ, List.mem_cons] at h ⊢
          rcases h with heq | hmem
          · exact Or.inl heq
          · exact Or.inr (ih hmem)

/-- An element an erased list holds is one the list holds. -/
theorem eraseAt_sublist (l : List Ref) (i : Nat) : (eraseAt l i).Sublist l := by
  induction l generalizing i with
  | nil => simp
  | cons y t ih =>
      cases i with
      | zero => exact List.Sublist.cons _ (List.Sublist.refl t)
      | succ n => exact List.Sublist.cons_cons _ (ih n)

/-! ## The heap the schema reads at a level

The schema's write resolves its path through the heap's cells: each level's index
picks the element out of the cell at hand's slots, and the level above has already
emptied the index it used. `resolve` is that routing, and it is the routing the
recursion below performs. -/

/-! ## The schema's checks and its two moves

The model of the runtime's exclusivity test is the count being one, and the schema
makes it at the cell at hand of every level and at the element it extracted. The
take-out and the put-back are the two moves the schema makes at a level: the
occurrence leaves the cell at hand's slots and the caller holds the element, and
later the element's reference goes back where it came from and the handle is
released. -/

/-- The modelled count of `r` at a configuration: the occurrences among the heap's
own slots plus the handles held outside the store. -/
def liveCount (c : CHeap) (hs : List Ref) (r : Ref) : Nat :=
  (CHeap.presentation c).occurrences r + hs.count r

/-- The modelled count is `Footprint.refCount` at the heap's presentation. -/
theorem liveCount_eq_refCount (c : CHeap) (hs : List Ref) (r : Ref) :
    liveCount c hs r = refCount (CHeap.presentation c) hs r := rfl

/-- The model of the runtime's exclusivity test at a cell: the count of `r` over
the heap's own slots and the handles held outside it is one. -/
def exclusive? (c : CHeap) (hs : List Ref) (r : Ref) : Bool :=
  liveCount c hs r == 1

/-- The check a write's operand has to pass: every reference the written slots
name is a live cell of the heap. -/
def namesLive (c : CHeap) (ks : List Ref) : Bool :=
  ks.all (fun x => decide (x ∈ CHeap.refs c))

/-- The check a write's operand has to pass at the cell it writes: the written
slots do not name that cell, so the write cannot make a cell name itself. -/
def avoids (ks : List Ref) (r : Ref) : Bool :=
  decide (r ∉ ks)

/-- The exclusivity test passing is the modelled `Exclusive`. -/
theorem exclusive?_eq_true {c : CHeap} {hs : List Ref} {r : Ref}
    (h : exclusive? c hs r = true) : Exclusive (CHeap.presentation c) hs r := by
  rw [exclusive?, beq_iff_eq, liveCount_eq_refCount] at h
  exact h

/-- The model's test reports exactly `Exclusive`, so a `#guard` on it is a check
of the count. -/
theorem exclusive?_eq_decide (c : CHeap) (hs : List Ref) (r : Ref) :
    exclusive? c hs r = true ↔ Exclusive (CHeap.presentation c) hs r := by
  rw [exclusive?, beq_iff_eq, liveCount_eq_refCount]
  exact Iff.rfl

/-- The test reports false exactly when the cell is not exclusively owned. -/
theorem exclusive?_eq_false (c : CHeap) (hs : List Ref) (r : Ref) :
    exclusive? c hs r = false ↔ ¬ Exclusive (CHeap.presentation c) hs r := by
  constructor
  · intro h hx
    rw [← exclusive?_eq_decide] at hx
    rw [h] at hx
    exact Bool.noConfusion hx
  · intro h
    cases hex : exclusive? c hs r with
    | true => exact absurd ((exclusive?_eq_decide c hs r).mp hex) h
    | false => rfl

/-- A write's operand that passes the liveness check names live cells only. -/
theorem namesLive_eq_true {c : CHeap} {ks : List Ref} (h : namesLive c ks = true) :
    ∀ x ∈ ks, x ∈ CHeap.refs c := by
  intro x hx
  rw [namesLive, List.all_eq_true] at h
  exact of_decide_eq_true (h x hx)

/-- A write's operand that passes the self-name check does not name the cell the
write lands at. -/
theorem avoids_eq_true {ks : List Ref} {r : Ref} (h : avoids ks r = true) : r ∉ ks := by
  simpa [avoids] using h

/-- The take-out at a level: the occurrence leaves the cell at hand's slots — the
take-out empties the slot it extracts from — and the caller's handle on the
extracted reference appears, so the reference is named by a handle where it was
named by the slot. The count is unchanged by the exchange: two names for two.

The pair the executor's take-out hands back is the next operation, not this one:
this is the extraction alone, which transfers the occurrence. -/
def takeOut (c : CHeap) (hs : List Ref) (r : Ref) (i : Nat) (e : Ref) :
    CHeap × List Ref :=
  dup (CHeap.writeSlots c r (eraseAt (CHeap.slotsAt c r) i)) hs e

/-- The put-back at a level: the element the recursion returns is installed at the
index the take-out emptied, and the handle that held it is released, so the
reference is named by the slot again where it was named by the handle.

The put-back writes the cell at hand's slots, so it carries the requirement the
counted heap makes of a write: the slots it installs do not name the cell it
writes. A put-back that does not meet it does not run. -/
def plug (c : CHeap) (hs : List Ref) (r : Ref) (i : Nat) (e : Ref) :
    Option (CHeap × List Ref) :=
  if avoids (putAt (CHeap.slotsAt c r) i e) r then
    some (decRef (CHeap.writeSlots c r (putAt (CHeap.slotsAt c r) i e)) hs e)
  else none

/-- The put-back's check passing is what lets it run: the slots it installs do not
name the cell at hand. -/
theorem plug_check {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    {c' : CHeap} {hs' : List Ref} (h : plug c hs r i e = some (c', hs')) :
    r ∉ putAt (CHeap.slotsAt c r) i e :=
  avoids_eq_true (by
    by_cases hchk : avoids (putAt (CHeap.slotsAt c r) i e) r = true
    · exact hchk
    · rw [plug, ite_eq_right hchk] at h
      exact absurd h (by simp))

/-- A put-back whose check passes is the release the schema performs. -/
theorem plug_eq_of_check {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    (h : avoids (putAt (CHeap.slotsAt c r) i e) r = true) :
    plug c hs r i e
      = some (decRef (CHeap.writeSlots c r (putAt (CHeap.slotsAt c r) i e)) hs e) := by
  rw [plug, ite_eq_left h]

/-- The heap a take-out leaves: the occurrence leaves the cell at hand's slots and
the caller's handle on the extracted reference appears. The handle list a take-out
returns holds that handle; the heap does not depend on it, which is why the schema's
routing can read the heap it leaves. -/
def held (c : CHeap) (r : Ref) (i : Nat) (e : Ref) : CHeap := (takeOut c [] r i e).1

/-- The cell a path addresses: the slot at the index names the next reference and
the index this level used no longer names anything, and the path below is then
resolved from that reference in the heap the take-out left. This is the routing the
schema's own write performs: the model of the path's indices is the model of the
lookups the recursion makes, so a path resolves exactly as the schema follows it.
`none` for an index the cell at hand's slots do not have. -/
def resolve : CHeap → Ref → Path → Option Ref
  | _, r, [] => some r
  | c, r, i :: p =>
      match (CHeap.slotsAt c r)[i]? with
      | some e => resolve (held c r i e) e p
      | none => none

/-- The root path addresses the cell at hand. -/
@[simp] theorem resolve_nil (c : CHeap) (r : Ref) : resolve c r [] = some r := rfl

/-- A level with an index its cell's slots do not have addresses nothing. -/
theorem resolve_cons_of_not_mem (c : CHeap) (r : Ref) (i : Nat) (p : Path)
    (h : (CHeap.slotsAt c r)[i]? = none) : resolve c r (i :: p) = none := by
  simp [resolve, h]

/-- A level's index picks its element out of the cell at hand's slots, and the path
below is resolved from that element in the heap the take-out left. -/
theorem resolve_cons (c : CHeap) (r : Ref) (i : Nat) (p : Path) (e : Ref)
    (h : (CHeap.slotsAt c r)[i]? = some e) :
    resolve c r (i :: p) = resolve (held c r i e) e p := by
  simp [resolve, h]

/-- The heap a take-out leaves is the one the model's `takeOut` returns, whichever
handle list it was handed. -/
@[simp] theorem takeOut_fst_held (c : CHeap) (hs : List Ref) (r : Ref) (i : Nat) (e : Ref) :
    (takeOut c hs r i e).1 = held c r i e := rfl

/-! ## The schema's write at a path

`writeStep` is the executor's write: at each array step the cell at hand is
checked, the element at the index is taken out — the occurrence becomes the
caller's handle — the take-out's pair is destructured so the pair's handle on the
element is dropped, the extracted element is checked on its own, the path below is
followed into it, and the element is put back at the index the take-out emptied
and the handle released; at the end of the path the leaf update, `RCHeap.update`,
is applied to the addressed cell's slots.

A step that does not run is `none`: an index the cell at hand's slots do not have,
a check that does not pass, or an operand that does not meet the counted heap's
requirements. The model has no panic, and the checks it makes are the executor's:
a run is the sequence of the steps that ran. -/
def writeStep : CHeap → List Ref → Ref → Path → List Ref → Option (CHeap × List Ref)
  | c, hs, r, [], ks =>
      if exclusive? c hs r && namesLive c ks && avoids ks r then
        some (update c hs r ks)
      else none
  | c, hs, r, i :: p, ks =>
      match (CHeap.slotsAt c r)[i]? with
      | none => none
      | some e =>
          if exclusive? c hs r then
            let held := takeOut c hs r i e
            let pair := dup held.1 held.2 e
            let released := decRef pair.1 pair.2 e
            if exclusive? released.1 released.2 e then
              match writeStep released.1 released.2 e p ks with
              | none => none
              | some rest => plug rest.1 rest.2 r i (rest.2.headD e)
            else none
          else none

/-- At a path with no level the schema's write is the leaf update at the cell at
hand, behind the three checks: the cell is exclusively owned, and the operand
names live cells and not the cell it writes. -/
theorem writeStep_nil (c : CHeap) (hs : List Ref) (r : Ref) (ks : List Ref) :
    writeStep c hs r [] ks =
      (if exclusive? c hs r && namesLive c ks && avoids ks r then
        some (update c hs r ks)
      else none) := rfl

/-- At a path with a level the schema looks the element up in the cell at hand's
slots, checks the cell, takes the element out with its pair, drops the pair's
handle, checks the extracted element, follows the path into it and puts it back. -/
theorem writeStep_cons (c : CHeap) (hs : List Ref) (r : Ref) (i : Nat) (p : Path)
    (ks : List Ref) :
    writeStep c hs r (i :: p) ks =
      (match (CHeap.slotsAt c r)[i]? with
       | none => none
       | some e =>
          if exclusive? c hs r then
            let held := takeOut c hs r i e
            let pair := dup held.1 held.2 e
            let released := decRef pair.1 pair.2 e
            if exclusive? released.1 released.2 e then
              match writeStep released.1 released.2 e p ks with
              | none => none
              | some rest => plug rest.1 rest.2 r i (rest.2.headD e)
            else none
          else none) := rfl

/-! ## The acceptance invariant

The predicate a run starts in and every step preserves: the heap is healthy, it is
`Counted` at the handles the run holds, and the run's handles are the runner's own
handle on the session's root and the references the issued read results hold — and
those name none. A read issues a `Footprint.Value` that names no reference, which
is the encoded observation the sealed surface's read returns, so the issued
results' handles are none and the run holds the root's handle once. -/

/-- The invariant a run starts in: the heap is healthy, every cell's count is the
aliasing `Footprint` counts for it, and the only handles the run holds are the
runner's own on the session's root and the references its issued read results
name — and an issued read result names no reference. -/
def Accept (root : Ref) (c : CHeap) (hs : List Ref) (vs : List Value) : Prop :=
  CHeap.Healthy c ∧ Counted c hs ∧
    (hs = root :: handlesOf vs ∧ ∀ v ∈ vs, Value.refs v = [])

/-- The heap of an accepted configuration is healthy. -/
theorem Accept.healthy {root : Ref} {c : CHeap} {hs : List Ref} {vs : List Value}
    (h : Accept root c hs vs) : CHeap.Healthy c := h.1

/-- An accepted configuration is counted at its handles. -/
theorem Accept.counted {root : Ref} {c : CHeap} {hs : List Ref} {vs : List Value}
    (h : Accept root c hs vs) : Counted c hs := h.2.1

/-- An accepted configuration's handles are the runner's own and the issued
results' references. -/
theorem Accept.handles {root : Ref} {c : CHeap} {hs : List Ref} {vs : List Value}
    (h : Accept root c hs vs) : hs = root :: handlesOf vs := h.2.2.1

/-- Every value an accepted configuration's run issued names no reference. -/
theorem Accept.issued {root : Ref} {c : CHeap} {hs : List Ref} {vs : List Value}
    (h : Accept root c hs vs) : ∀ v ∈ vs, Value.refs v = [] := h.2.2.2

/-- A list of issued read results none of which names a reference holds no
handle. -/
theorem handlesOf_eq_nil_of_detached {vs : List Value}
    (h : ∀ v ∈ vs, Value.refs v = []) : handlesOf vs = [] := by
  induction vs with
  | nil => rfl
  | cons v rest ih =>
      rw [handlesOf_cons, h v (by simp), List.nil_append]
      exact ih fun w hw => h w (by simp [hw])

/-- An accepted configuration's issued results hold no handle: their references
are none. -/
theorem Accept.handlesOf_eq_nil {root : Ref} {c : CHeap} {hs : List Ref}
    {vs : List Value} (h : Accept root c hs vs) : handlesOf vs = [] :=
  handlesOf_eq_nil_of_detached h.issued

/-- An accepted configuration's handle list is the runner's own handle alone. -/
theorem Accept.handles_eq_cons_nil {root : Ref} {c : CHeap} {hs : List Ref}
    {vs : List Value} (h : Accept root c hs vs) : hs = [root] := by
  rw [h.handles, h.handlesOf_eq_nil]

/-- The runner's own handle names the session's root: an accepted configuration's
handle list holds it. -/
theorem Accept.root_mem {root : Ref} {c : CHeap} {hs : List Ref} {vs : List Value}
    (h : Accept root c hs vs) : root ∈ hs := by
  rw [h.handles]
  exact List.mem_cons_self ..

/-! ## Programs and runs

A program is the sequence of steps a run performs: a read at a path, which returns
a value and leaves the heap and the handles alone, and a write at a path, which is
the schema above. -/

/-- One step of a program: a read at a path, whose result the run issues, and a
write at a path, which is the schema's write of the slots `ks`. -/
inductive Cmd where
  /-- A read at a path: the value it returned is issued to the run. -/
  | read (p : Path) (v : Value)
  /-- A write at a path: the addressed cell's slots become `ks`. -/
  | write (p : Path) (ks : List Ref)

/-- A program: the steps a run performs, in order. -/
abbrev Prog := List Cmd

/-- One step's semantics: a read leaves the heap and the handles alone and issues
the value it read, which names no reference; a write is the schema's write at the
path, which the step's `some` reports. -/
inductive Step (root : Ref) :
    CHeap → List Ref → List Value → Cmd → CHeap → List Ref → List Value → Prop where
  /-- A read: the heap and the handles are the ones it was handed, and the value
  it read — an observation naming no reference — joins the issued results. -/
  | read {c : CHeap} {hs : List Ref} {vs : List Value} {p : Path} {v : Value}
      (hdet : Value.refs v = []) : Step root c hs vs (.read p v) c hs (v :: vs)
  /-- A write: the schema's write at the path, which is a step exactly when it
  reports a result. -/
  | write {c : CHeap} {hs : List Ref} {vs : List Value} {p : Path} {ks : List Ref}
      {c' : CHeap} {hs' : List Ref} (h : writeStep c hs root p ks = some (c', hs')) :
      Step root c hs vs (.write p ks) c' hs' vs

/-- A run of a program from a configuration to the one it leaves. -/
inductive Run (root : Ref) :
    CHeap → List Ref → List Value → Prog → CHeap → List Ref → List Value → Prop where
  /-- The empty program: nothing runs and the configuration is the one handed. -/
  | nil {c : CHeap} {hs : List Ref} {vs : List Value} : Run root c hs vs [] c hs vs
  /-- A step and the run of the program after it. -/
  | cons {c : CHeap} {hs : List Ref} {vs : List Value} {cmd : Cmd}
      {c₁ : CHeap} {hs₁ : List Ref} {vs₁ : List Value} {rest : Prog}
      {c₂ : CHeap} {hs₂ : List Ref} {vs₂ : List Value} :
      Step root c hs vs cmd c₁ hs₁ vs₁ → Run root c₁ hs₁ vs₁ rest c₂ hs₂ vs₂ →
      Run root c hs vs (cmd :: rest) c₂ hs₂ vs₂

/-! ## The arithmetic of the two moves

The take-out's erasure removes one occurrence — the extracted reference's — and
nothing else, and the put-back installs one — the element's reference. The four
facts below are what the counting lemmas need of the two list moves, and the frame
lemmas after them are what the addresses need: a write at one reference leaves
every other reference's slots and reads alone. -/

/-- The element an erasure removed is the one that index held. -/
theorem eraseAt_count_self {l : List Ref} {i : Nat} {e : Ref} (h : l[i]? = some e) :
    (eraseAt l i).count e = l.count e - 1 := by
  induction l generalizing i with
  | nil => simp at h
  | cons y t ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp
      | succ n =>
          simp only [List.getElem?_cons_succ] at h
          have hpos : 1 ≤ t.count e :=
            List.one_le_count_iff.mpr (List.mem_iff_getElem?.mpr ⟨n, h⟩)
          rw [eraseAt_succ]
          by_cases hy : y = e
          · subst hy
            rw [List.count_cons_self, List.count_cons_self, ih h]
            omega
          · rw [List.count_cons_of_ne hy, List.count_cons_of_ne hy, ih h]

/-- An erasure leaves every other reference's occurrences alone. -/
theorem eraseAt_count_of_ne {l : List Ref} {i : Nat} {e : Ref} {y : Ref} (hy : y ≠ e)
    (h : l[i]? = some e) : (eraseAt l i).count y = l.count y := by
  induction l generalizing i with
  | nil => simp at h
  | cons z t ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          rw [eraseAt_zero]
          by_cases hz : z = y
          · exact absurd hz.symm hy
          · rw [List.count_cons_of_ne hz]
      | succ n =>
          simp only [List.getElem?_cons_succ] at h
          rw [eraseAt_succ]
          by_cases hz : z = y
          · subst hz
            rw [List.count_cons_self, List.count_cons_self, ih h]
          · rw [List.count_cons_of_ne hz, List.count_cons_of_ne hz, ih h]

/-- The element a put-back installs is the one it adds. -/
theorem putAt_count_self (l : List Ref) (i : Nat) (x : Ref) :
    (putAt l i x).count x = l.count x + 1 := by
  induction l generalizing i with
  | nil => cases i <;> simp
  | cons z t ih =>
      cases i with
      | zero => simp
      | succ n =>
          rw [putAt_succ]
          by_cases hz : z = x
          · subst hz
            rw [List.count_cons_self, List.count_cons_self, ih n]
          · rw [List.count_cons_of_ne hz, List.count_cons_of_ne hz, ih n]

/-- A put-back leaves every other reference's occurrences alone. -/
theorem putAt_count_of_ne (l : List Ref) (i : Nat) (x : Ref) (y : Ref) (hy : y ≠ x) :
    (putAt l i x).count y = l.count y := by
  induction l generalizing i with
  | nil =>
      cases i with
      | zero => rw [putAt_nil, List.count_cons_of_ne (b := x) (a := y) (fun hh => hy hh.symm)]
      | succ n => rw [putAt_nil, List.count_cons_of_ne (b := x) (a := y) (fun hh => hy hh.symm)]
  | cons z t ih =>
      cases i with
      | zero =>
          rw [putAt_zero]
          by_cases hz : z = y
          · rw [← hz, List.count_cons_of_ne (b := x) (a := z) (fun hh => hy (hh.trans hz).symm)]
          · rw [List.count_cons_of_ne (b := x) (a := y) (fun hh => hy hh.symm),
              List.count_cons_of_ne hz]
      | succ n =>
          rw [putAt_succ]
          by_cases hz : z = y
          · subst hz
            rw [List.count_cons_self, List.count_cons_self, ih n]
          · rw [List.count_cons_of_ne hz, List.count_cons_of_ne hz, ih n]

/-- A destructive write at one reference leaves every other reference's slots
alone: it changes one cell's slots, and it moves counts rather than slots. -/
theorem CHeap.lookup_writeSlots_of_ne (c : CHeap) (r : Ref) (ks : List Ref) {x : Ref}
    (hx : x ≠ r) : CHeap.lookup (CHeap.writeSlots c r ks) x = CHeap.lookup c x := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · rw [h, CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_self,
          CHeap.lookup_cons_of_ne (r := x) (r' := r) (fun hh => hx hh.symm),
          CHeap.lookup_cons_of_ne (r := x) (r' := r) (fun hh => hx hh.symm),
          CHeap.lookup_map_shiftCell]
      · rw [CHeap.writeSlots_eq, CHeap.writeSlotsAux_cons_of_ne h, shiftCell_pair]
        by_cases hx' : r' = x
        · rw [hx', CHeap.lookup_cons_self, CHeap.lookup_cons_self]
          simp
        · rw [CHeap.lookup_cons_of_ne (r := x) (r' := r') (fun hh => hx' hh),
            CHeap.lookup_cons_of_ne (r := x) (r' := r') (fun hh => hx' hh)]
          exact ih

/-- A destructive write at one reference leaves every other reference's slots
alone. -/
theorem CHeap.slotsAt_writeSlots_of_ne (c : CHeap) (r : Ref) (ks : List Ref) {x : Ref}
    (hx : x ≠ r) : CHeap.slotsAt (CHeap.writeSlots c r ks) x = CHeap.slotsAt c x := by
  simp [CHeap.slotsAt, CHeap.lookup_writeSlots_of_ne c r ks hx]

/-- A count adjustment changes no slots, so it changes no cell's read. -/
theorem CHeap.slotsAt_adjust (c : CHeap) (r : Ref) (f : Nat → Nat) (x : Ref) :
    CHeap.slotsAt (CHeap.adjust c r f) x = CHeap.slotsAt c x := by
  simp [CHeap.slotsAt, CHeap.lookup_adjust]

/-- Every reference the slots of the cell at hand name is a live cell. -/
theorem mem_refs_of_mem_slotsAt {c : CHeap} {hs : List Ref} (hc : Counted c hs) {r : Ref}
    (hr : r ∈ CHeap.refs c) {x : Ref} (h : x ∈ CHeap.slotsAt c r) : x ∈ CHeap.refs c :=
  Classical.byContradiction fun hx => by
    have hzero : (CHeap.slots c).count x = 0 := Counted.slots_count_eq_zero hc hx
    have hle := CHeap.slotsAt_count_le_slots c r hr x
    have : (CHeap.slotsAt c r).count x = 0 := by omega
    rw [List.count_eq_zero] at this
    exact this h

/-- A heap's slots are occurrences at references it lists. -/
theorem mem_refs_of_mem_slots {c : CHeap} {hs : List Ref} (hc : Counted c hs) {x : Ref}
    (h : x ∈ CHeap.slots c) : x ∈ CHeap.refs c :=
  Classical.byContradiction fun hx => by
    have hzero : (CHeap.slots c).count x = 0 := Counted.slots_count_eq_zero hc hx
    rw [List.count_eq_zero] at hzero
    exact hzero h

/-- A handle names a live cell. -/
theorem mem_refs_of_handle {c : CHeap} {hs : List Ref} (hc : Counted c hs) {x : Ref}
    (h : x ∈ hs) : x ∈ CHeap.refs c :=
  Classical.byContradiction fun hx => by
    have hzero : hs.count x = 0 := Counted.handles_count_eq_zero hc hx
    rw [List.count_eq_zero] at hzero
    exact hzero h


/-! ## The take-out and the put-back

The two moves of a level, with the facts the induction carries: the take-out's heap
names the extracted reference exactly as often as the heap it was handed, and the
put-back's heap likewise, so both preserve the invariant; and each leaves every
slot list but the cell at hand's alone, which is what the addresses need. -/

/-- A cell at hand whose read found an element is a live cell. -/
theorem mem_refs_of_slotsAt_getElem? {c : CHeap} {r : Ref} {i : Nat} {e : Ref}
    (h : (CHeap.slotsAt c r)[i]? = some e) : r ∈ CHeap.refs c :=
  Classical.byContradiction fun hr => by
    have h0 := CHeap.slotsAt_of_not_mem (c := c) (r := r) hr
    rw [h0] at h
    simp at h

/-- A reference the cell at hand's slots name is one the heap's slots name. -/
theorem mem_slots_of_mem_slotsAt {c : CHeap} {r : Ref} (hr : r ∈ CHeap.refs c) {x : Ref}
    (h : x ∈ CHeap.slotsAt c r) : x ∈ CHeap.slots c := by
  have hpos : 0 < (CHeap.slotsAt c r).count x := List.count_pos_iff.mpr h
  have hle := CHeap.slotsAt_count_le_slots c r hr x
  exact List.count_pos_iff.mp (by omega)

/-- The written cell's slot list is the write's own slots. -/
theorem CHeap.slotsAt_writeSlots_self (c : CHeap) (r : Ref) (ks : List Ref)
    (hr : r ∈ CHeap.refs c) : CHeap.slotsAt (CHeap.writeSlots c r ks) r = ks := by
  simp [CHeap.slotsAt, CHeap.lookup_writeSlots_self c r ks hr]

/-- A destructive write's count at every reference: the written cell's own count is
untouched, another live cell's count moves by the change in the occurrences that
name it, and a reference the heap does not list has no count. -/
theorem CHeap.count_writeSlots (c : CHeap) (r : Ref) (ks : List Ref)
    (hr : r ∈ CHeap.refs c) (hlive : ∀ y ∈ ks, y ∈ CHeap.refs c) (x : Ref) :
    CHeap.count (CHeap.writeSlots c r ks) x
      = (if x = r then CHeap.count c x
         else CHeap.count c x - (CHeap.slotsAt c r).count x + ks.count x) := by
  by_cases hx : x = r
  · rw [ite_eq_left hx, hx, CHeap.count_writeSlots_self c r ks hr]
  · rw [ite_eq_right hx]
    by_cases hxm : x ∈ CHeap.refs c
    · exact CHeap.count_writeSlots_of_ne c r ks hx hxm hr
    · rw [CHeap.count_writeSlots_not_mem c r ks hxm, CHeap.count_eq_zero_of_not_mem hxm,
        List.count_eq_zero.mpr (fun hmem => hxm (hlive x hmem))]
      simp

/-- A count raised at a reference and lowered again at it is the count it was: the
pair's increment and the decrement that drops the pair's handle cancel. -/
theorem CHeap.adjust_add_one_sub_one (c : CHeap) (r : Ref) :
    CHeap.adjust (CHeap.adjust c r (· + 1)) r (· - 1) = c := by
  induction c with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨r', cl⟩ := e
      by_cases h : r' = r
      · rw [h, CHeap.adjust_cons_self, CHeap.adjust_cons_self]
        simp
      · rw [CHeap.adjust_cons_of_ne h, CHeap.adjust_cons_of_ne h, ih]

/-- The take-out's handle list is the caller's handle on the extracted reference
followed by the handles the caller held. -/
@[simp] theorem takeOut_handles (c : CHeap) (hs : List Ref) (r : Ref) (i : Nat) (e : Ref) :
    (takeOut c hs r i e).2 = e :: hs := rfl

/-- The take-out's heap lists the references the heap it was handed listed. -/
theorem takeOut_refs (c : CHeap) (hs : List Ref) (r : Ref) (i : Nat) (e : Ref) :
    CHeap.refs (takeOut c hs r i e).1 = CHeap.refs c := by
  simp [takeOut, dup, CHeap.refs_adjust, CHeap.refs_writeSlots]

/-- The take-out's heap names the extracted reference exactly as often as the heap
it was handed: the occurrence became the caller's handle, two names for two. -/
theorem takeOut_count_eq {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    (hc : Counted c hs) (hlook : (CHeap.slotsAt c r)[i]? = some e) (hne : e ≠ r) (x : Ref) :
    CHeap.count (takeOut c hs r i e).1 x = CHeap.count c x := by
  have hr : r ∈ CHeap.refs c := mem_refs_of_slotsAt_getElem? hlook
  have hbound : ∀ y, (CHeap.slotsAt c r).count y ≤ CHeap.count c y := fun y => by
    have h := (counted_iff_slots c hs).mp hc y
    have hle := CHeap.slotsAt_count_le_slots c r hr y
    omega
  have hne' : (CHeap.slotsAt c r).count e ≤ CHeap.count c e := hbound e
  have hpos : 1 ≤ (CHeap.slotsAt c r).count e :=
    List.one_le_count_iff.mpr (List.mem_iff_getElem?.mpr ⟨i, hlook⟩)
  show CHeap.count
      (CHeap.adjust (CHeap.writeSlots c r (eraseAt (CHeap.slotsAt c r) i)) e (· + 1)) x
    = CHeap.count c x
  by_cases hx : x = e
  · rw [hx]
    have heslots : e ∈ CHeap.slots c :=
      mem_slots_of_mem_slotsAt hr (List.mem_iff_getElem?.mpr ⟨i, hlook⟩)
    have her : e ∈ CHeap.refs c := mem_refs_of_mem_slots hc heslots
    have herW : e ∈ CHeap.refs (CHeap.writeSlots c r (eraseAt (CHeap.slotsAt c r) i)) := by
      rw [CHeap.refs_writeSlots]
      exact her
    rw [CHeap.count_adjust_self _ e (· + 1) herW,
      CHeap.count_writeSlots_of_ne c r (eraseAt (CHeap.slotsAt c r) i) hne her hr,
      eraseAt_count_self hlook]
    rw [Nat.add_assoc, Nat.sub_add_cancel hpos, Nat.sub_add_cancel hne']
  · rw [CHeap.count_adjust_of_ne _ e (· + 1) hx]
    by_cases hxr : x = r
    · rw [hxr, CHeap.count_writeSlots_self c r (eraseAt (CHeap.slotsAt c r) i) hr]
    · have hkslive : ∀ y ∈ eraseAt (CHeap.slotsAt c r) i, y ∈ CHeap.refs c := fun y hy =>
        mem_refs_of_mem_slots hc (mem_slots_of_mem_slotsAt hr (mem_eraseAt hy))
      rw [CHeap.count_writeSlots c r (eraseAt (CHeap.slotsAt c r) i) hr hkslive x,
        ite_eq_right hxr, eraseAt_count_of_ne hx hlook, Nat.sub_add_cancel (hbound x)]

/-- The take-out preserves `Counted`: the occurrence left the cell at hand's slots
and the caller's handle appears. -/
theorem takeOut_counted {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    (hc : Counted c hs) (hr : r ∈ CHeap.refs c) (hlook : (CHeap.slotsAt c r)[i]? = some e)
    (hks : r ∉ eraseAt (CHeap.slotsAt c r) i) (hself : r ∉ CHeap.slotsAt c r)
    (hlive : ∀ x ∈ eraseAt (CHeap.slotsAt c r) i, x ∈ CHeap.refs c) :
    Counted (takeOut c hs r i e).1 (takeOut c hs r i e).2 := by
  have hc₁ : Counted (CHeap.writeSlots c r (eraseAt (CHeap.slotsAt c r) i)) hs :=
    counted_writeSlots hc hr hks hself hlive
  have he₁ : e ∈ CHeap.refs (CHeap.writeSlots c r (eraseAt (CHeap.slotsAt c r) i)) := by
    rw [CHeap.refs_writeSlots]
    exact mem_refs_of_mem_slots hc (mem_slots_of_mem_slotsAt hr
      (List.mem_iff_getElem?.mpr ⟨i, hlook⟩))
  exact counted_dup hc₁ he₁

/-- The take-out's heap's slot list at the cell at hand is the one the take-out
emptied, the extracted occurrence gone. -/
theorem takeOut_slotsAt {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    (hlook : (CHeap.slotsAt c r)[i]? = some e) :
    CHeap.slotsAt (takeOut c hs r i e).1 r = eraseAt (CHeap.slotsAt c r) i := by
  have hr : r ∈ CHeap.refs c := mem_refs_of_slotsAt_getElem? hlook
  simp [takeOut, dup, CHeap.slotsAt_adjust, CHeap.slotsAt_writeSlots_self c r _ hr]

/-- The take-out preserves the invariant: its heap's counts are the counts the heap
had and it lists the same references, so it is as healthy as the heap it was
handed. -/
theorem takeOut_healthy {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    (h : CHeap.Healthy c) (hc : Counted c hs) (hlook : (CHeap.slotsAt c r)[i]? = some e)
    (hne : e ≠ r) : CHeap.Healthy (takeOut c hs r i e).1 := by
  obtain ⟨hW, hl⟩ := h
  have hrs : r ∈ CHeap.refs c := mem_refs_of_slotsAt_getElem? hlook
  have hW' : CHeap.WF (takeOut c hs r i e).1 := by
    rw [CHeap.WF, takeOut_refs]
    exact hW
  refine ⟨hW', ?_⟩
  rw [CHeap.live_iff_refs hW']
  intro x hx
  rw [takeOut_refs] at hx
  rw [takeOut_count_eq hc hlook hne x]
  exact (CHeap.live_iff_refs hW).mp hl x hx

/-- The pair's increment and the drop of the pair's handle cancel on the heap: the
discipline's drop takes the pair's handle out, and the count it had raised goes
down with it. -/
theorem pair_dup_decRef_fst (c : CHeap) (hs : List Ref) (r : Ref) :
    (decRef (dup c hs r).1 (dup c hs r).2 r).1 = c := by
  simp [dup, decRef, CHeap.adjust_add_one_sub_one]

/-- The pair's increment and the drop of the pair's handle cancel on the handle
list: the drop releases the handle the increment added. -/
theorem pair_dup_decRef_snd (c : CHeap) (hs : List Ref) (r : Ref) :
    (decRef (dup c hs r).1 (dup c hs r).2 r).2 = hs := by
  simp [dup, decRef]

/-- A put-back's count at every reference: it installs one occurrence of the
element in the cell at hand's slots and leaves every other occurrence alone. -/
theorem putAt_count (l : List Ref) (i : Nat) (x : Ref) (y : Ref) :
    (putAt l i x).count y = l.count y + (if y = x then 1 else 0) := by
  by_cases h : y = x
  · rw [ite_eq_left h, h, putAt_count_self]
  · rw [ite_eq_right h, putAt_count_of_ne l i x y h, Nat.add_zero]

/-- An element a put-back installed is the installed one or a slot the list had. -/
theorem mem_putAt {l : List Ref} {i : Nat} {y : Ref} {x : Ref} (h : x ∈ putAt l i y) :
    x = y ∨ x ∈ l := by
  induction l generalizing i with
  | nil =>
      cases i with
      | zero => exact Or.inl (by simpa using h)
      | succ n => exact Or.inl (by simpa using h)
  | cons z t ih =>
      cases i with
      | zero =>
          rw [putAt_zero] at h
          rcases List.mem_cons.mp h with heq | hmem
          · exact Or.inl heq
          · rcases List.mem_cons.mp hmem with heq | hmem'
            · exact Or.inr (by rw [heq]; exact List.mem_cons_self ..)
            · exact Or.inr (List.mem_cons_of_mem z hmem')
      | succ n =>
          rw [putAt_succ] at h
          rcases List.mem_cons.mp h with heq | hmem
          · exact Or.inr (by rw [heq]; exact List.mem_cons_self ..)
          · rcases ih hmem with hy | hmem'
            · exact Or.inl hy
            · exact Or.inr (List.mem_cons_of_mem z hmem')

/-- The put-back's heap lists the references the heap it was handed listed. -/
theorem plug_refs {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    {c' : CHeap} {hs' : List Ref} (h : plug c hs r i e = some (c', hs')) :
    CHeap.refs c' = CHeap.refs c := by
  have hchk : avoids (putAt (CHeap.slotsAt c r) i e) r = true :=
    decide_eq_true_iff.mpr (plug_check h)
  rw [plug_eq_of_check hchk] at h
  cases Option.some.inj h
  simp [CHeap.refs_adjust, CHeap.refs_writeSlots]

/-- The put-back's heap names every reference exactly as often as the heap it was
handed: one occurrence moves from the handle to the cell at hand's slots. -/
theorem plug_count_eq {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    (hc : Counted c hs) (hr : r ∈ CHeap.refs c) (he : e ∈ CHeap.refs c) (hne : e ≠ r)
    {c' : CHeap} {hs' : List Ref} (h : plug c hs r i e = some (c', hs')) (x : Ref) :
    CHeap.count c' x = CHeap.count c x := by
  have hchk : avoids (putAt (CHeap.slotsAt c r) i e) r = true :=
    decide_eq_true_iff.mpr (plug_check h)
  rw [plug_eq_of_check hchk] at h
  cases Option.some.inj h
  have hkslive : ∀ y ∈ putAt (CHeap.slotsAt c r) i e, y ∈ CHeap.refs c := fun y hy => by
    rcases mem_putAt hy with hye | hmem
    · rw [hye]; exact he
    · exact mem_refs_of_mem_slots hc (mem_slots_of_mem_slotsAt hr hmem)
  show CHeap.count
      (CHeap.adjust (CHeap.writeSlots c r (putAt (CHeap.slotsAt c r) i e)) e (· - 1)) x
    = CHeap.count c x
  by_cases hx : x = e
  · rw [hx]
    have heW : e ∈ CHeap.refs (CHeap.writeSlots c r (putAt (CHeap.slotsAt c r) i e)) := by
      rw [CHeap.refs_writeSlots]
      exact he
    rw [CHeap.count_adjust_self _ e (· - 1) heW,
      CHeap.count_writeSlots_of_ne c r (putAt (CHeap.slotsAt c r) i e) hne he hr,
      putAt_count (CHeap.slotsAt c r) i e e, ite_eq_left rfl]
    have hB : (CHeap.slotsAt c r).count e ≤ CHeap.count c e := by
      have h := (counted_iff_slots c hs).mp hc e
      have hle := CHeap.slotsAt_count_le_slots c r hr e
      omega
    have hinner : CHeap.count c e - (CHeap.slotsAt c r).count e
        + ((CHeap.slotsAt c r).count e + 1) = CHeap.count c e + 1 := by
      rw [← Nat.add_assoc, Nat.sub_add_cancel hB]
    rw [hinner, Nat.add_sub_cancel]
  · rw [CHeap.count_adjust_of_ne _ e (· - 1) hx]
    by_cases hxr : x = r
    · rw [hxr, CHeap.count_writeSlots_self c r (putAt (CHeap.slotsAt c r) i e) hr]
    · rw [CHeap.count_writeSlots c r (putAt (CHeap.slotsAt c r) i e) hr hkslive x,
        ite_eq_right hxr, putAt_count (CHeap.slotsAt c r) i e x, ite_eq_right hx,
        Nat.add_zero]
      have hB : (CHeap.slotsAt c r).count x ≤ CHeap.count c x := by
        have h := (counted_iff_slots c hs).mp hc x
        have hle := CHeap.slotsAt_count_le_slots c r hr x
        omega
      rw [Nat.sub_add_cancel hB]

/-- The put-back preserves `Counted`: the occurrence returns to the cell at hand's
slots and the handle that held it is released. -/
theorem plug_counted {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    (hc : Counted c hs) (hr : r ∈ CHeap.refs c) (hself : r ∉ CHeap.slotsAt c r)
    (hlive : ∀ x ∈ putAt (CHeap.slotsAt c r) i e, x ∈ CHeap.refs c)
    (hhandle : 1 ≤ hs.count e)
    {c' : CHeap} {hs' : List Ref} (h : plug c hs r i e = some (c', hs')) :
    Counted c' hs' := by
  have hchk : avoids (putAt (CHeap.slotsAt c r) i e) r = true :=
    decide_eq_true_iff.mpr (plug_check h)
  rw [plug_eq_of_check hchk] at h
  cases Option.some.inj h
  exact counted_decRef
    (counted_writeSlots hc hr (avoids_eq_true hchk) hself hlive) hhandle

/-- The put-back preserves the invariant: its counts are the counts the heap had
and it lists the same references. -/
theorem plug_healthy {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    (h : CHeap.Healthy c) (hc : Counted c hs) (hr : r ∈ CHeap.refs c) (he : e ∈ CHeap.refs c)
    {c' : CHeap} {hs' : List Ref} (hpl : plug c hs r i e = some (c', hs')) (hne : e ≠ r) :
    CHeap.Healthy c' := by
  have hW' : CHeap.WF c' := by
    rw [CHeap.WF, plug_refs hpl]
    exact h.1
  refine ⟨hW', ?_⟩
  rw [CHeap.live_iff_refs hW']
  intro x hx
  rw [plug_refs hpl] at hx
  rw [plug_count_eq hc hr he hne hpl x]
  exact (CHeap.live_iff_refs h.1).mp h.2 x hx

/-- The put-back's heap's slot list at the cell at hand is the erased list with the
element installed where the take-out emptied it. -/
theorem plug_slotsAt {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    {c' : CHeap} {hs' : List Ref} (hr : r ∈ CHeap.refs c)
    (h : plug c hs r i e = some (c', hs')) :
    CHeap.slotsAt c' r = putAt (CHeap.slotsAt c r) i e := by
  have hchk : avoids (putAt (CHeap.slotsAt c r) i e) r = true :=
    decide_eq_true_iff.mpr (plug_check h)
  rw [plug_eq_of_check hchk] at h
  cases Option.some.inj h
  simp [CHeap.slotsAt_adjust, CHeap.slotsAt_writeSlots_self c r _ hr]

/-- A put-back at one cell leaves every other cell's read alone. -/
theorem plug_lookup_of_ne {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    {c' : CHeap} {hs' : List Ref} (h : plug c hs r i e = some (c', hs')) {x : Ref}
    (hx : x ≠ r) : c'.lookup x = CHeap.lookup c x := by
  have hchk : avoids (putAt (CHeap.slotsAt c r) i e) r = true :=
    decide_eq_true_iff.mpr (plug_check h)
  rw [plug_eq_of_check hchk] at h
  cases Option.some.inj h
  rw [CHeap.lookup_adjust, CHeap.lookup_writeSlots_of_ne c r _ hx]

/-- The put-back's handles release the one the caller held on the element. -/
theorem plug_handles {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {e : Ref}
    {c' : CHeap} {hs' : List Ref} (h : plug c hs r i e = some (c', hs')) :
    hs' = dropHandle hs e := by
  have hchk : avoids (putAt (CHeap.slotsAt c r) i e) r = true :=
    decide_eq_true_iff.mpr (plug_check h)
  rw [plug_eq_of_check hchk] at h
  cases Option.some.inj h
  rfl

/-! ## The write step's statement

The schema's write lands its slots at the address its path resolves to: the leaf
update runs at a cell of count one, so it takes the destructive branch and the
addressed cell keeps its location, and the take-outs' handles and the put-backs
leave every cell but the addressed one where it was. -/

/-- A write step's check at the cell at hand passes: a path is walked only from a
cell that holds one. -/
theorem writeStep_check {c : CHeap} {hs : List Ref} {r : Ref} {p : Path} {ks : List Ref}
    {c' : CHeap} {hs' : List Ref} (h : writeStep c hs r p ks = some (c', hs')) :
    exclusive? c hs r = true := by
  cases p with
  | nil =>
      rw [writeStep_nil] at h
      by_cases hchk : (exclusive? c hs r && namesLive c ks && avoids ks r) = true
      · exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hchk).1).1
      · rw [ite_eq_right hchk] at h
        exact absurd h (by simp)
  | cons i p' =>
      rw [writeStep_cons] at h
      split at h
      · exact absurd h (by simp)
      · rename_i e hlook
        by_cases hchk : exclusive? c hs r = true
        · exact hchk
        · rw [ite_eq_right hchk] at h
          exact absurd h (by simp)

/-- A cell whose count is one and whose handle list's head is the cell's own
reference is named by that one handle and by no slot. -/
theorem exclusive_head {c : CHeap} {hs : List Ref} {r : Ref}
    (hes : Exclusive (CHeap.presentation c) hs r) (hhead : hs.head? = some r) :
    (CHeap.slots c).count r = 0 ∧ hs.count r = 1 ∧ hs.tail.count r = 0 := by
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp hhead
  have htail : hs.tail = rest := by rw [hrest]; rfl
  have hcount : hs.count r = rest.count r + 1 := by
    rw [hrest, List.count_cons_self]
  have href : refCount (CHeap.presentation c) hs r = 1 := hes
  rw [refCount, CHeap.occurrences_presentation, hcount] at href
  exact ⟨by omega, by omega, by rw [htail]; omega⟩

/-- The reference a handle list's head names is one it holds. -/
theorem mem_of_head?_eq_some {l : List Ref} {r : Ref} (h : l.head? = some r) : r ∈ l := by
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp h
  rw [hrest]
  exact List.mem_cons_self ..

/-- A handle list whose head is a reference is that reference followed by the
list's tail. -/
theorem eq_cons_tail_of_head?_eq_some {l : List Ref} {r : Ref} (h : l.head? = some r) :
    l = r :: l.tail := by
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp h
  rw [hrest]
  rfl

/-- A list's tail is a sublist of the list. -/
theorem tail_sublist (l : List Ref) : l.tail.Sublist l := by
  cases l with
  | nil => exact List.Sublist.refl []
  | cons y t =>
      rw [List.tail_cons]
      exact List.Sublist.cons y (List.Sublist.refl t)

/-- The handle list's tail holds the head's reference one time fewer. -/
theorem count_tail_of_head {l : List Ref} {r : Ref} (h : l.head? = some r) :
    l.count r = l.tail.count r + 1 := by
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp h
  rw [hrest, List.tail_cons, List.count_cons_self]

/-- A released handle list is a sublist of the list it released from. -/
theorem dropHandle_sublist (l : List Ref) (r : Ref) : (dropHandle l r).Sublist l := by
  induction l with
  | nil => exact List.Sublist.refl []
  | cons y t ih =>
      by_cases hy : y = r
      · rw [hy, dropHandle_cons_self]
        exact List.Sublist.cons r (List.Sublist.refl t)
      · rw [dropHandle_cons_of_ne hy]
        exact List.Sublist.cons_cons y ih

/-- A reference a released handle list holds is one the list held. -/
theorem mem_of_mem_dropHandle {l : List Ref} {x r : Ref} (h : x ∈ dropHandle l r) : x ∈ l :=
  (dropHandle_sublist l r).subset h

/-- The cascade lists references the heap it ran on listed. -/
theorem mem_refs_cascadeSteps {n : Nat} {c : CHeap} {x : Ref}
    (h : x ∈ CHeap.refs (CHeap.cascadeSteps n c)) : x ∈ CHeap.refs c := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih =>
      cases hfind : c.find? (fun e => e.2.count == 0) with
      | none =>
          rw [CHeap.cascadeSteps_eq_none hfind] at h
          exact h
      | some e =>
          have h1 : x ∈ CHeap.refs (CHeap.cascadeSteps n (CHeap.dealloc c e.1)) := by
            have hh := h
            rw [CHeap.cascadeSteps_succ_some hfind] at hh
            exact hh
          have h3 : x ∈ dropHandle (CHeap.refs c) e.1 := by
            have h2 := ih h1
            rwa [CHeap.refs_dealloc] at h2
          exact mem_of_mem_dropHandle h3

/-- The cascade lists references the heap it ran on listed. -/
theorem mem_refs_cascade {c : CHeap} {x : Ref} (h : x ∈ CHeap.refs (CHeap.cascade c)) :
    x ∈ CHeap.refs c :=
  mem_refs_cascadeSteps h

/-- An element a put-back installs was in the list it was handed. -/
theorem mem_putAt_of_mem : ∀ (l : List Ref) (i : Nat) (y : Ref) (x : Ref), x ∈ l → x ∈ putAt l i y
  | [], _, _, _, h => by simp at h
  | z :: t, 0, y, x, h => by
      rw [putAt_zero]
      exact List.mem_cons_of_mem y h
  | z :: t, n + 1, y, x, h => by
      rw [putAt_succ]
      rcases List.mem_cons.mp h with heq | hmem
      · rw [heq]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem z (mem_putAt_of_mem t n y x hmem)

/-- **The write step's statement.** A write step at a path from a cell at hand that
holds one, in a healthy heap counted at the run's handles, lands the written slots
at the address the path resolves to — the leaf update runs at a cell of count one
and therefore takes the destructive branch — and leaves the handle list, the heap's
health and its counting as they were, with the addressed cell's only name the
handle the write holds. -/
theorem writeStep_spec {c : CHeap} {hs : List Ref} {r : Ref} {p : Path} {ks : List Ref}
    (hH : CHeap.Healthy c) (hC : Counted c hs) (hhead : hs.head? = some r) :
    ∀ {c' : CHeap} {hs' : List Ref} {t : Ref}, resolve c r p = some t →
      writeStep c hs r p ks = some (c', hs') →
      c'.lookup t = some ks ∧ hs' = hs ∧ CHeap.Healthy c' ∧ Counted c' hs' ∧
        (∀ x ∈ CHeap.refs c', x ∈ CHeap.refs c) ∧ (hs.tail).count t = 0 := by
  intro c' hs' t haddr h
  induction p generalizing c hs r ks c' hs' t with
  | nil =>
      rw [writeStep_nil] at h
      simp only [resolve_nil, Option.some.injEq] at haddr
      subst haddr
      by_cases hchk : (exclusive? c hs r && namesLive c ks && avoids ks r) = true
      · rw [ite_eq_left hchk] at h
        obtain ⟨hcheck, hoperand⟩ := Bool.and_eq_true_iff.mp hchk
        have hex : exclusive? c hs r = true := (Bool.and_eq_true_iff.mp hcheck).1
        have hlive : ∀ x ∈ ks, x ∈ CHeap.refs c :=
          namesLive_eq_true (Bool.and_eq_true_iff.mp hcheck).2
        have hks : r ∉ ks := avoids_eq_true hoperand
        have hes : Exclusive (CHeap.presentation c) hs r := exclusive?_eq_true hex
        obtain ⟨hclean, hhold, htail⟩ := exclusive_head hes hhead
        have hcount : CHeap.count c r = 1 := (counted_iff_exclusive hC r).mpr hes
        have hupd : update c hs r ks = (c', hs') := Option.some.inj h
        rw [update_of_count_one c hs r ks hcount] at hupd
        obtain ⟨rfl, rfl⟩ := hupd
        have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by omega)
        have hself : r ∉ CHeap.slotsAt c r := by
          intro hmem
          have hpos : 0 < (CHeap.slotsAt c r).count r := List.count_pos_iff.mpr hmem
          have hle := CHeap.slotsAt_count_le_slots c r hr r
          omega
        refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
        · simpa [update_of_count_one c hs r ks hcount] using
            update_preserves_location_of_exclusive hH.1 hC hes (by omega) hks
        · have hh : CHeap.Healthy (update c hs r ks).1 :=
            ⟨CHeap.wf_update hH.1, CHeap.live_update hH⟩
          simpa [update_of_count_one c hs r ks hcount] using hh
        · simpa [update_of_count_one c hs r ks hcount] using
            counted_update_exclusive hH.1 hC hes hks hself hlive
        · intro x hx
          have h1 := mem_refs_cascade hx
          rwa [CHeap.refs_writeSlots] at h1
        · exact htail
      · rw [ite_eq_right hchk] at h
        exact absurd h (by simp)
  | cons i p' ih =>
      rw [writeStep_cons] at h
      cases hlook : (CHeap.slotsAt c r)[i]? with
      | none =>
          simp only [hlook] at h
          exact absurd h (by simp)
      | some e =>
          simp only [hlook] at h
          by_cases hchk : exclusive? c hs r = true
          · rw [ite_eq_left hchk] at h
            have hex : Exclusive (CHeap.presentation c) hs r := exclusive?_eq_true hchk
            obtain ⟨hclean, hhold, htailr⟩ := exclusive_head hex hhead
            have hcount : CHeap.count c r = 1 := (counted_iff_exclusive hC r).mpr hex
            have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by omega)
            have hself : r ∉ CHeap.slotsAt c r := by
              intro hmem
              have hpos : 0 < (CHeap.slotsAt c r).count r := List.count_pos_iff.mpr hmem
              have hle := CHeap.slotsAt_count_le_slots c r hr r
              omega
            have hne : e ≠ r := by
              intro heq
              have hmem : e ∈ CHeap.slotsAt c r := List.mem_iff_getElem?.mpr ⟨i, hlook⟩
              rw [heq] at hmem
              exact hself hmem
            have heslots : e ∈ CHeap.slots c :=
              mem_slots_of_mem_slotsAt hr (List.mem_iff_getElem?.mpr ⟨i, hlook⟩)
            have her : e ∈ CHeap.refs c := mem_refs_of_mem_slots hC heslots
            have hkserase : r ∉ eraseAt (CHeap.slotsAt c r) i := fun hmem => hself (mem_eraseAt hmem)
            have hliverase : ∀ x ∈ eraseAt (CHeap.slotsAt c r) i, x ∈ CHeap.refs c :=
              fun x hx => mem_refs_of_mem_slots hC (mem_slots_of_mem_slotsAt hr (mem_eraseAt hx))
            have hcT : Counted (takeOut c hs r i e).1 (takeOut c hs r i e).2 :=
              takeOut_counted hC hr hlook hkserase hself hliverase
            have hhT : CHeap.Healthy (takeOut c hs r i e).1 := takeOut_healthy hH hC hlook hne
            have hheadT : (takeOut c hs r i e).2.head? = some e := by rw [takeOut_handles]; rfl
            simp only [pair_dup_decRef_fst, pair_dup_decRef_snd] at h
            by_cases hfoc : exclusive? (takeOut c hs r i e).1 (takeOut c hs r i e).2 e = true
            · rw [ite_eq_left hfoc] at h
              cases hdeep : writeStep (takeOut c hs r i e).1 (takeOut c hs r i e).2 e p' ks with
              | none =>
                  rw [hdeep] at h
                  exact absurd h (by simp)
              | some rest =>
                  rw [hdeep] at h
                  have hpl : plug rest.1 rest.2 r i (rest.2.headD e) = some (c', hs') := h
                  have haddr' : resolve (takeOut c hs r i e).1 e p' = some t := by
                    rw [takeOut_fst_held, ← resolve_cons c r i p' e hlook]
                    exact haddr
                  obtain ⟨hlookT, hlistT, hHT, hCT, hsubT, hexpT⟩ :=
                    ih hhT hcT hheadT haddr' hdeep
                  have hrest : rest.2 = e :: hs := by rw [hlistT, takeOut_handles]
                  have hheadD : rest.2.headD e = e := by rw [hrest]; rfl
                  have heinrest : e ∈ rest.2 := by rw [hrest]; exact List.mem_cons_self ..
                  have heR : e ∈ CHeap.refs rest.1 := mem_refs_of_handle hCT heinrest
                  have hrR : r ∈ CHeap.refs rest.1 := by
                    apply CHeap.mem_refs_of_count_pos
                    have hcs := (counted_iff_slots rest.1 rest.2).mp hCT r
                    have hc2 : rest.2.count r = 1 := by
                      rw [hrest, List.count_cons_of_ne (b := e) (a := r) hne, hhold]
                    omega
                  have hcountT : rest.2.count e = hs.count e + 1 := by
                    rw [hrest, List.count_cons_self]
                  have hexpT' : hs.count t = 0 := by
                    have hh := hexpT
                    rw [takeOut_handles, List.tail_cons] at hh
                    exact hh
                  have htne : t ≠ r := by
                    intro heq
                    have hpos : 1 ≤ hs.count r := List.one_le_count_iff.mpr (mem_of_head?_eq_some hhead)
                    rw [heq] at hexpT'
                    omega
                  have hselfR : r ∉ CHeap.slotsAt rest.1 r := by
                    intro hmem
                    exact plug_check hpl (mem_putAt_of_mem (CHeap.slotsAt rest.1 r) i
                      (rest.2.headD e) r hmem)
                  have hliveR : ∀ x ∈ putAt (CHeap.slotsAt rest.1 r) i (rest.2.headD e),
                      x ∈ CHeap.refs rest.1 := by
                    intro x hx
                    rcases mem_putAt hx with heq | hmem
                    · rw [heq, hheadD]
                      exact heR
                    · exact mem_refs_of_mem_slots hCT (mem_slots_of_mem_slotsAt hrR hmem)
                  have hhandleR : 1 ≤ rest.2.count (rest.2.headD e) := by
                    rw [hheadD, hcountT]
                    omega
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                  · rw [plug_lookup_of_ne hpl (x := t) htne]
                    exact hlookT
                  · rw [plug_handles hpl, hheadD, hrest, dropHandle_cons_self]
                  · refine plug_healthy hHT hCT hrR ?_ hpl ?_
                    · rw [hheadD]
                      exact heR
                    · rw [hheadD]
                      exact hne
                  · exact plug_counted hCT hrR hselfR hliveR hhandleR hpl
                  · intro x hx
                    rw [plug_refs hpl] at hx
                    have h1 := hsubT x hx
                    rwa [takeOut_refs] at h1
                  · have hle := List.Sublist.count_le t (tail_sublist hs)
                    omega
            · rw [ite_eq_right hfoc] at h
              exact absurd h (by simp)
          · rw [ite_eq_right hchk] at h
            exact absurd h (by simp)

/-- A write step's path resolves: the lookups the schema makes are the lookups the
resolution makes, so a step that reports a result addresses a cell. -/
theorem writeStep_resolve {c : CHeap} {hs : List Ref} {r : Ref} {p : Path} {ks : List Ref}
    (h : ∃ c' hs', writeStep c hs r p ks = some (c', hs')) :
    ∃ t, resolve c r p = some t := by
  induction p generalizing c hs r ks with
  | nil => exact ⟨r, rfl⟩
  | cons i p' ih =>
      obtain ⟨c', hs', hw⟩ := h
      rw [writeStep_cons] at hw
      cases hlook : (CHeap.slotsAt c r)[i]? with
      | none =>
          simp only [hlook] at hw
          exact absurd hw (by simp)
      | some e =>
          simp only [hlook] at hw
          by_cases hchk : exclusive? c hs r = true
          · rw [ite_eq_left hchk] at hw
            simp only [pair_dup_decRef_fst, pair_dup_decRef_snd] at hw
            by_cases hfoc : exclusive? (takeOut c hs r i e).1 (takeOut c hs r i e).2 e = true
            · rw [ite_eq_left hfoc] at hw
              cases hdeep : writeStep (takeOut c hs r i e).1 (takeOut c hs r i e).2 e p' ks with
              | none =>
                  rw [hdeep] at hw
                  exact absurd hw (by simp)
              | some rest =>
                  cases rest with
                  | mk d₁ d₂ =>
                      obtain ⟨t, ht⟩ := ih ⟨d₁, d₂, hdeep⟩
                      exact ⟨t, by rw [resolve_cons c r i p' e hlook]; exact ht⟩
            · rw [ite_eq_right hfoc] at hw
              exact absurd hw (by simp)
          · rw [ite_eq_right hchk] at hw
            exact absurd hw (by simp)

/-- A write step whose result is written as one value resolves its path. -/
theorem writeStep_resolve_of_eq {c : CHeap} {hs : List Ref} {r : Ref} {p : Path}
    {ks : List Ref} {x : CHeap × List Ref} (h : writeStep c hs r p ks = some x) :
    ∃ t, resolve c r p = some t := by
  cases x with
  | mk c' hs' => exact writeStep_resolve ⟨c', hs', h⟩

/-- The schema's write at the root path is applied at a cell of count one: the leaf
update's own check makes the cell at hand exclusive, and `counted_iff_exclusive`
reads that as the count the update branches on. At a longer path the same check is
made about the addressed cell: the level above it checks the element it took out
before the recursion enters it. -/
theorem writeStep_leaf_count {c : CHeap} {hs : List Ref} {r : Ref} {ks : List Ref}
    {c' : CHeap} {hs' : List Ref} (hC : Counted c hs)
    (h : writeStep c hs r [] ks = some (c', hs')) : CHeap.count c r = 1 :=
  (counted_iff_exclusive hC r).mpr (exclusive?_eq_true (writeStep_check h))

/-- **The per-step statement.** At a write step of an accepted configuration the leaf
update runs at a cell of count one — the schema's focus check makes that cell's
`exclusive?` pass, and `counted_iff_exclusive` reads it as the count the update
branches on — so by `update_preserves_location_of_exclusive` it takes the
destructive branch: the addressed cell keeps its location and holds the written
slots, the handle list is what it was, and the configuration stays accepted. -/
theorem writeStep_lands {root : Ref} {c : CHeap} {hs : List Ref} {vs : List Value}
    {p : Path} {ks : List Ref} {c' : CHeap} {hs' : List Ref} {t : Ref}
    (hacc : Accept root c hs vs) (haddr : resolve c root p = some t)
    (h : writeStep c hs root p ks = some (c', hs')) :
    c'.lookup t = some ks ∧ hs' = hs ∧ Accept root c' hs' vs := by
  have hhead : hs.head? = some root := by
    rw [hacc.handles]
    rfl
  obtain ⟨hlook, hlist, hHT, hCT, hsub, hexp⟩ :=
    writeStep_spec hacc.healthy hacc.counted hhead haddr h
  exact ⟨hlook, hlist, hHT, hCT, by rw [hlist]; exact hacc.handles, hacc.issued⟩

/-- The acceptance invariant is preserved by a write step: the step's heap is
healthy, it is counted at the handles it left — which are the ones it was handed —
and the runner's own handle and the issued results' references are what they were. -/
theorem writeStep_accept {root : Ref} {c : CHeap} {hs : List Ref} {vs : List Value}
    {p : Path} {ks : List Ref} {c' : CHeap} {hs' : List Ref}
    (hacc : Accept root c hs vs) (h : writeStep c hs root p ks = some (c', hs')) :
    Accept root c' hs' vs := by
  obtain ⟨t, ht⟩ := writeStep_resolve ⟨c', hs', h⟩
  exact (writeStep_lands hacc ht h).2.2

/-- A read step leaves an accepted configuration accepted: the value it issues names
no reference, so the handles the run holds are what they were. -/
theorem readStep_accept {root : Ref} {c : CHeap} {hs : List Ref} {vs : List Value}
    {v : Value} (hacc : Accept root c hs vs) (hdet : Value.refs v = []) :
    Accept root c hs (v :: vs) := by
  refine ⟨hacc.healthy, hacc.counted, ?_, ?_⟩
  · rw [hacc.handles, handlesOf_cons, hdet, List.nil_append]
  · intro w hw
    rcases List.mem_cons.mp hw with heq | hmem
    · rw [heq]; exact hdet
    · exact hacc.issued w hmem

/-- Every step preserves the acceptance invariant. -/
theorem step_accept {root : Ref} {c : CHeap} {hs : List Ref} {vs : List Value}
    {cmd : Cmd} {c' : CHeap} {hs' : List Ref} {vs' : List Value}
    (h : Step root c hs vs cmd c' hs' vs') (hacc : Accept root c hs vs) :
    Accept root c' hs' vs' := by
  cases h with
  | read hdet => exact readStep_accept hacc hdet
  | write hw => exact writeStep_accept hacc hw

/-- A run from an accepted configuration leaves an accepted configuration: the
invariant holds at every step of the sequence. -/
theorem run_accept {root : Ref} {c : CHeap} {hs : List Ref} {vs : List Value}
    {prog : Prog} {c' : CHeap} {hs' : List Ref} {vs' : List Value}
    (h : Run root c hs vs prog c' hs' vs') (hacc : Accept root c hs vs) :
    Accept root c' hs' vs' := by
  induction h with
  | nil => exact hacc
  | cons hstep _ ih => exact ih (step_accept hstep hacc)

/-- A run of a program that begins with another program splits into a run of the
first and a run of the rest. -/
theorem run_append {root : Ref} {c : CHeap} {hs : List Ref} {vs : List Value}
    {pre rest : Prog} {c' : CHeap} {hs' : List Ref} {vs' : List Value}
    (h : Run root c hs vs (pre ++ rest) c' hs' vs') :
    ∃ c₁ hs₁ vs₁, Run root c hs vs pre c₁ hs₁ vs₁ ∧
      Run root c₁ hs₁ vs₁ rest c' hs' vs' := by
  induction pre generalizing c hs vs with
  | nil => exact ⟨c, hs, vs, Run.nil, by simpa using h⟩
  | cons cmd pre' ih =>
      cases h with
      | cons hstep hrest =>
          obtain ⟨c₁, hs₁, vs₁, hpre, hrest'⟩ := ih hrest
          exact ⟨c₁, hs₁, vs₁, Run.cons hstep hpre, hrest'⟩

/-- **The per-run statement.** Every write step of the execution of an accepted
program is destructive at the address it writes and leaves that address unchanged:
the step's leaf update runs at a cell of count one — the schema's focus check makes
that cell's `exclusive?` pass — so it takes the destructive branch, and the heap the
step leaves reads the written slots back where the path's address was. -/
theorem every_write_step_keeps_its_address {root : Ref} {c : CHeap} {hs : List Ref}
    {vs : List Value} {prog : Prog} {c' : CHeap} {hs' : List Ref} {vs' : List Value}
    (hacc : Accept root c hs vs) (h : Run root c hs vs prog c' hs' vs')
    {pre : Prog} {p : Path} {ks : List Ref} {suf : Prog}
    (hsplit : pre ++ Cmd.write p ks :: suf = prog) :
    ∃ (c₁ : CHeap) (hs₁ : List Ref) (vs₁ : List Value) (t : Ref) (c₂ : CHeap)
      (hs₂ : List Ref),
      Run root c hs vs pre c₁ hs₁ vs₁ ∧ resolve c₁ root p = some t ∧
        writeStep c₁ hs₁ root p ks = some (c₂, hs₂) ∧ c₂.lookup t = some ks ∧
        hs₂ = hs₁ := by
  have h' : Run root c hs vs ((pre ++ [Cmd.write p ks]) ++ suf) c' hs' vs' := by
    rw [List.append_assoc, List.singleton_append, hsplit]
    exact h
  obtain ⟨d₁, d₂, d₃, hd₁, _⟩ := run_append h'
  obtain ⟨c₁, hs₁, vs₁, hpre, hsteprun⟩ := run_append hd₁
  cases hsteprun with
  | cons hstep _ =>
      cases hstep with
      | write hw =>
          have hacc₁ : Accept root c₁ hs₁ vs₁ := run_accept hpre hacc
          obtain ⟨t, ht⟩ := writeStep_resolve_of_eq hw
          obtain ⟨hlook, hlist, _⟩ := writeStep_lands hacc₁ ht hw
          exact ⟨c₁, hs₁, vs₁, t, _, _, hpre, ht, hw, hlook, hlist⟩

/-- **The countermodel.** The same write with the schema's drop removed: the
take-out's handle is still held when the write runs, so the addressed cell's count
is two, the update below it is not applied at a cell of count one, and it copies —
the written slots land at a fresh location rather than at the addressed cell's own.

This is Trap 1, the shape the in-place check's `layout5-checked-unique` case failed
on: the check fires on a uniquely owned array until the pair the take-out handed
back is destructured, because the handle the pair still holds is the second
reference to the element. -/
theorem pair_handle_held_copies {c : CHeap} {hs : List Ref} {e : Ref} {ks : List Ref}
    (hC : Counted c (e :: e :: hs)) (h0 : (CHeap.slots c).count e = 0)
    (hhs : hs.count e = 0) (hks : e ∉ ks) :
    CHeap.count c e = 2 ∧ ¬ Exclusive (CHeap.presentation c) (e :: e :: hs) e ∧
      (update c (e :: e :: hs) e ks).1.lookup (fresh c ks) = some ks := by
  have hcount : CHeap.count c e = 2 := by
    have h := (counted_iff_slots c (e :: e :: hs)).mp hC e
    rw [h0] at h
    simp only [List.count_cons_self] at h
    omega
  have hne : ¬ Exclusive (CHeap.presentation c) (e :: e :: hs) e := by
    intro hex
    have h1 : CHeap.count c e = 1 := (counted_iff_exclusive hC e).mpr hex
    omega
  exact ⟨hcount, hne,
    (update_copies_of_shared hC hne (by simp) hks).1⟩

/-- The same write with the schema's drop present: the pair's handle is released
before the focus check, the addressed cell's count is one, and the update keeps its
location. -/
theorem pair_handle_dropped_keeps {c : CHeap} {hs : List Ref} {e : Ref} {ks : List Ref}
    (hW : CHeap.WF c) (hC : Counted c (e :: e :: hs)) (h0 : (CHeap.slots c).count e = 0)
    (hhs : hs.count e = 0) (hks : e ∉ ks) :
    (update (decRef c (e :: e :: hs) e).1 (decRef c (e :: e :: hs) e).2 e ks).1.lookup e
      = some ks := by
  have hcount : CHeap.count c e = 2 := by
    have h := (counted_iff_slots c (e :: e :: hs)).mp hC e
    rw [h0] at h
    simp only [List.count_cons_self] at h
    omega
  have hdrop : Counted (decRef c (e :: e :: hs) e).1 (decRef c (e :: e :: hs) e).2 :=
    counted_decRef hC (by simp)
  have her : e ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by omega)
  have hcount' : CHeap.count (decRef c (e :: e :: hs) e).1 e = 1 := by
    simp only [decRef]
    rw [CHeap.count_adjust_self c e (· - 1) her, hcount]
  have hex : Exclusive (CHeap.presentation (decRef c (e :: e :: hs) e).1)
      (decRef c (e :: e :: hs) e).2 e := (counted_iff_exclusive hdrop e).mp hcount'
  have hhandle : 1 ≤ (decRef c (e :: e :: hs) e).2.count e := by
    simp only [decRef]
    rw [dropHandle_cons_self, List.count_cons_self, hhs]
    omega
  refine update_preserves_location_of_exclusive (c := (decRef c (e :: e :: hs) e).1)
    (handles := (decRef c (e :: e :: hs) e).2) (r := e) (ks := ks)
    (CHeap.wf_decRef hW) hdrop hex hhandle hks
