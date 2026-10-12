/-
Checks for `Scidonia.FracPerm.StateVar.Run`.

The module is a run of the counted heap: a program is the sequence of steps a run
performs, a path is the slot indices a write follows, the schema's write at a path
is the executor's — the array check, the take-out that transfers an occurrence into
the caller's handle, the drop of the take-out's pair before the focus check, the
recursion into the extracted element, and the put-back — and the leaf update is the
counted heap's own. Its per-step statement is that the write lands its slots at the
address its path resolves to, and its per-run statement is that every write step of
an accepted program's execution is destructive there. A proof module has no
pre-fix behaviour to observe, so the checks here meet its definitions and theorems
from outside, on heaps and programs a client of the module can build. They are of
six kinds:

* **The checks and the routing, evaluated**, as `#guard`s: the exclusivity test at
  the cells of a small heap, the cell a path resolves to at each depth, and whether
  a write step runs. Each detector has an affirmative control beside it — a false
  equation of the same `#guard` shape whose message is pinned — so a guard is shown
  to fire rather than to pass whatever it is given.
* **The write's own result**, as `#guard`s of the heap and the handle list a write
  step leaves: the write at the chain's middle cell empties that cell's slots, its
  cascade frees the cell the emptied slot named, and the runner is left holding the
  root's handle alone; and a write that would make the addressed cell name itself,
  or name a cell the heap does not list, does not run at all.
* **Negative controls as theorems about specific heaps and paths**: the pair a
  take-out hands back makes the extracted cell's count two, so the update below it
  is not applied at a cell of count one and copies — the shape the in-place check's
  `layout5-checked-unique` case failed on — and it stands beside an affirmative
  handle list at the *same* heap and path: the same write with the pair's handle
  dropped keeps the cell's location.
* **The per-step statement**, as `writeStep_lands` applied at the chain: the path's
  address is the middle cell and the write lands the written slots there, and the
  configuration the step leaves is accepted.
* **The per-run statement**, as `every_write_step_keeps_its_address` applied at a
  program of a read and a write: the split names the write step, and the theorem
  gives the cell that step addressed and the heap it left.
* **Axioms**: each representative theorem's `#print axioms` output is pinned to the
  standard kernel principles, so a proof that acquires any other axiom fails the
  build rather than printing a longer list for a reader to notice.

The heaps below are read as exactly the cells they list, which is the reading
`Counted` is stated under; nothing here constructs a heap from a compiled run.
-/
import Scidonia.FracPerm.StateVar.Run

open Scidonia.FracPerm.StateVar
open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap
open Scidonia.FracPerm.StateVar.Run

namespace ScidoniaTest.Run

/-! ## The heaps the checks are read at -/

/-- A chain of three cells: the root's one slot names the middle cell, the middle
cell's one slot names the leaf, the leaf's slots name nothing, and the one handle
names the root. Every cell's count is one. -/
def chain : CHeap :=
  [(0, { slots := [1], count := 1 }), (1, { slots := [2], count := 1 }),
    (2, { slots := [], count := 1 })]

/-- The chain a write at the middle cell's path leaves: that cell's slots are
emptied, and the cell its old slot named is freed by the write's cascade. -/
def upper : CHeap :=
  [(0, { slots := [1], count := 1 }), (1, { slots := [], count := 1 })]

/-- The cell a take-out extracted, held by the pair's two handles and named by no
slot: the configuration the pair's handles leave. -/
def pair : CHeap := [(0, { slots := [], count := 2 })]

/-- The same, with the extracted cell's own slot naming a leaf: the configuration
whose update copies and whose heap the copy is read back from. -/
def pairCarrying : CHeap :=
  [(0, { slots := [1], count := 2 }), (1, { slots := [], count := 1 })]

/-- The run's handle list: the runner's own handle, and the handles the issued read
results hold — a read issues a value naming no reference, so there are none. -/
def handles : List Ref := [0]

/-! ## Counting the heaps

`Counted` is a statement about every reference, so a small heap is counted by hand:
its cells' counts are read off the occurrences and the handles, and the heaps here
are closed — every slot names a cell they list and every handle names one — which is
what lets the reference the heap does not list be discharged. -/

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

/-- The chain is counted at the runner's one handle: the root's count is the
handle's, and each other cell's count is the one slot occurrence that names it. -/
theorem chain_counted : Counted chain handles := by
  refine counted_of chain handles ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by simpa [chain] using hx
    rcases hx' with rfl | rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 1 ∨ x = 2 := by simpa [chain] using hx
    rcases hx' with rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 0 := by simpa [handles] using hx
    rw [hx']
    decide

/-- The chain carries no counted-zero cell. -/
theorem chain_live : CHeap.Live chain := by rw [CHeap.Live]; decide

/-- The chain's references are duplicate-free. -/
theorem chain_wf : CHeap.WF chain := by rw [CHeap.WF]; decide

/-- The chain is a heap the theorems that need both invariants at once are stated
about. -/
theorem chain_healthy : CHeap.Healthy chain := ⟨chain_wf, chain_live⟩

/-- The chain is accepted: it is healthy, counted at the runner's handle, and that
handle is the runner's own — the issued results are none, so they hold no handle. -/
theorem chain_accept : Accept 0 chain handles [] :=
  ⟨chain_healthy, chain_counted, by simp [handles, handlesOf], by simp⟩

/-- The take-out's pair leaves a heap the pair's two handles count: the extracted
cell's count is the two handles that name it. -/
theorem pair_counted : Counted pair [0, 0] := by
  refine counted_of pair [0, 0] ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 := by simpa [pair] using hx
    rw [hx']
    decide
  · intro x hx
    simp [pair] at hx
  · intro x hx
    have hx' : x = 0 := by simpa using hx
    rw [hx']
    decide

/-- The same pair shape with the extracted cell carrying a slot: the pair's handles
count the cell at two and the slot's reference at one. -/
theorem pairCarrying_counted : Counted pairCarrying [0, 0] := by
  refine counted_of pairCarrying [0, 0] ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 := by simpa [pairCarrying] using hx
    rcases hx' with rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 1 := by simpa [pairCarrying] using hx
    rw [hx']
    decide
  · intro x hx
    have hx' : x = 0 := by simpa using hx
    rw [hx']
    decide

/-! ## The checks, the routing and the write's result, evaluated

Every `#guard` below is answered by an affirmative control: a false equation of the
same shape whose reported message is pinned, so the guard is shown to fire and not
to pass whatever it is given. -/

/-
The runner's handle names the root: the root's count is one, so a write at it is
applied at a cell of count one.
-/
#guard decide (exclusive? chain handles 0)

/--
error: Expression
  decide (exclusive? chain handles 0 = false)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (exclusive? chain handles 0 = false)

/-
The pair a take-out hands back makes the extracted cell's count two: one handle is
the caller's, the other the pair's, and no slot names the cell, so the cell is not
exclusively owned.
-/
#guard decide (exclusive? pair [0, 0] 0 = false)

/--
error: Expression
  decide (exclusive? pair [0, 0] 0 = true)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (exclusive? pair [0, 0] 0 = true)

/-
The pair's increment and the drop cancel: the handle list the drop leaves is the
caller's own, the extracted cell's count is back to one, and it is exclusive again.
-/
#guard decide ((decRef pair [0, 0] 0).2 = [0])
#guard decide (CHeap.count (decRef pair [0, 0] 0).1 0 = 1)
#guard decide (exclusive? (decRef pair [0, 0] 0).1 (decRef pair [0, 0] 0).2 0)

/-
The path resolves: the root path addresses the cell at hand, the chain's first
index the middle cell, and the second the leaf.
-/
#guard decide (resolve chain 0 [] = some 0)
#guard decide (resolve chain 0 [0] = some 1)
#guard decide (resolve chain 0 [0, 0] = some 2)

/--
error: Expression
  decide (resolve chain 0 [0, 0] = some 1)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (resolve chain 0 [0, 0] = some 1)

/-
An index the cell at hand's slots do not have addresses nothing, and so does an
index whose cell's slots are too short.
-/
#guard decide (resolve chain 0 [1] = none)
#guard decide (resolve chain 0 [0, 1] = none)

/-
The write at the middle cell's path runs, and the heap it leaves is the chain with
that cell's slots emptied: the emptied slot named the leaf, which the write's
cascade frees, and the runner holds the root's handle alone.
-/
#guard decide (writeStep chain handles 0 [0] [] = some (upper, handles))

/--
error: Expression
  decide (writeStep chain handles 0 [0] [] = some (chain, handles))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (writeStep chain handles 0 [0] [] = some (chain, handles))

/-
A write's operand has to meet the counted heap's requirements: an operand that
would make the addressed cell name itself does not run, and neither does one that
names a cell the heap does not list.
-/
#guard decide (writeStep chain handles 0 [0, 0] [2] = none)
#guard decide (writeStep chain handles 0 [0, 0] [9] = none)

/--
error: Expression
  decide (writeStep chain handles 0 [0, 0] [] = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (writeStep chain handles 0 [0, 0] [] = none)

/-! ## The write's own result, at the chain

The write at the middle cell's path is destructive: the addressed cell keeps its
location and holds the written slots, the reference its old slot named is dropped,
and the heap the step leaves lists no cell that reference named. -/

/-- The heap the write leaves reads the written slots back at the middle cell, and
the write's own result is that heap with the runner's handle. -/
theorem upper_write_result :
    upper.lookup 1 = some [] ∧ writeStep chain handles 0 [0] [] = some (upper, handles) :=
  ⟨by decide, by decide⟩

/-- The write's cascade leaves no cell the dropped reference named: the leaf is gone
from the heap and from the heap's slots. -/
theorem upper_write_freed :
    CHeap.count upper 2 = 0 ∧ 2 ∉ CHeap.refs upper ∧ (CHeap.slots upper).count 2 = 0 :=
  ⟨by decide, by decide, by decide⟩

/-! ## The per-step statement, applied at the chain -/

/-- The per-step statement at the chain: the write at the middle cell's path lands
its slots at the address the path resolves to — the leaf update ran at a cell of
count one and took the destructive branch, so the addressed cell kept its location
— and the configuration the step leaves is accepted. -/
theorem chain_writeStep_lands :
    resolve chain 0 [0] = some 1 ∧ upper.lookup 1 = some []
      ∧ Accept 0 upper handles [] := by
  have hstep : writeStep chain handles 0 [0] [] = some (upper, handles) := by decide
  have ht : resolve chain 0 [0] = some 1 := by decide
  obtain ⟨hlook, hlist, hacc⟩ := writeStep_lands chain_accept ht hstep
  exact ⟨ht, hlook, hacc⟩

/-- The leaf update's own count-one fact at the chain: the write at the root path
runs — the cell at hand holds one and the operand meets the counted heap's
requirements — so the update is applied at a cell of count one and takes the
destructive branch, whose result is the write's own slots and the handle list it was
handed. -/
theorem chain_root_write_count :
    (writeStep chain handles 0 [] []).isSome = true ∧ CHeap.count chain 0 = 1
      ∧ (writeStep chain handles 0 [] []).map (fun q => q.1 = CHeap.cascade (CHeap.writeSlots chain 0 [])
          ∧ q.2 = handles) = some (True ∧ True) := by
  have hstep : writeStep chain handles 0 [] []
      = some (CHeap.cascade (CHeap.writeSlots chain 0 []), handles) := by decide
  refine ⟨by decide, writeStep_leaf_count chain_counted hstep, ?_⟩
  rw [hstep]
  simp only [Option.map_some, eq_self_iff_true, and_self]

/-! ## The countermodel and its affirmative control

The pair's handle is what the trap turns on: with it still held the write below the
extracted cell is applied at a cell of count two and copies, and with it dropped the
same write keeps the cell's location. At the same heap and path, these are the two
branches the in-place check's `layout5-checked-unique` case separates. -/

/-- The countermodel at the pair's heap: the extracted cell's count is two, it is
not exclusive, and the update below it copies — the written slots land at a fresh
location rather than at the cell's own. -/
theorem pair_held_copies :
    CHeap.count pair 0 = 2 ∧ ¬ Exclusive (CHeap.presentation pair) [0, 0] 0
      ∧ (update pair [0, 0] 0 []).1.lookup (fresh pair []) = some [] := by
  have h0 : (CHeap.slots pair).count 0 = 0 := by decide
  obtain ⟨hcount, hne, hlook⟩ := pair_handle_held_copies (ks := []) pair_counted h0 (by decide) (by decide)
  exact ⟨hcount, hne, hlook⟩

/-- The affirmative control at the same heap and path: with the pair's handle
dropped the cell holds one, and the same update keeps its location. -/
theorem pair_dropped_keeps :
    (update (decRef pair [0, 0] 0).1 (decRef pair [0, 0] 0).2 0 []).1.lookup 0 = some [] := by
  refine pair_handle_dropped_keeps (by rw [CHeap.WF]; decide) pair_counted (by decide)
    (by decide) (by decide)

/-- The same two branches at the pair shape whose extracted cell carries a slot: the
update below it copies at a fresh location with the pair's handle held, and keeps
the cell's location with it dropped. -/
theorem pairCarrying_branches :
    (update pairCarrying [0, 0] 0 []).1.lookup (fresh pairCarrying []) = some []
      ∧ (update (decRef pairCarrying [0, 0] 0).1 (decRef pairCarrying [0, 0] 0).2 0 []).1.lookup 0
        = some [] := by
  have h0 : (CHeap.slots pairCarrying).count 0 = 0 := by decide
  refine ⟨(pair_handle_held_copies (ks := []) pairCarrying_counted h0 (by decide) (by decide)).2.2, ?_⟩
  exact pair_handle_dropped_keeps (by rw [CHeap.WF]; decide) pairCarrying_counted (by decide)
    (by decide) (by decide)

/-! ## The per-run statement, applied at a program -/

/-- The program the per-run check runs: a read at the root path, whose value names
no reference, and then a write at the middle cell's path. -/
def prog : Prog := [Cmd.read [] Value.unit, Cmd.write [0] []]

/-- The program's execution: the read leaves the heap and the handles alone, and the
write is the chain's step. -/
theorem prog_run : Run 0 chain handles [] prog upper handles [Value.unit] :=
  Run.cons (Step.read rfl)
    (Run.cons (Step.write (c' := upper) (hs' := handles) (by decide)) Run.nil)

/-- The per-run statement at that program: the split names the write step, and the
step's address is the middle cell — the write's slots are read back there — while
the handle list is what the read left. -/
theorem prog_run_write_keeps_the_address :
    ∃ (c₁ : CHeap) (hs₁ : List Ref) (vs₁ : List Value) (t : Ref) (c₂ : CHeap) (hs₂ : List Ref),
      Run 0 chain handles [] [Cmd.read [] Value.unit] c₁ hs₁ vs₁
        ∧ resolve c₁ 0 [0] = some t ∧ writeStep c₁ hs₁ 0 [0] [] = some (c₂, hs₂)
        ∧ c₂.lookup t = some [] ∧ hs₂ = hs₁ :=
  every_write_step_keeps_its_address chain_accept prog_run
    (pre := [Cmd.read [] Value.unit]) (suf := []) rfl

/-- The write step the split names is the chain's own step: the read left the heap
alone, so the step's address is the middle cell, its slots are read back there, and
the heap the run ends at is the write's own result. -/
theorem prog_write_keeps_the_address :
    Run 0 chain handles [] prog upper handles [Value.unit]
      ∧ writeStep chain handles 0 [0] [] = some (upper, handles)
      ∧ upper.lookup 1 = some [] :=
  ⟨prog_run, by decide, by decide⟩

/-! ## Axioms of representative theorems

The facts above are proved with `simp`, `rw`, `decide`, `omega` and the model's own
recursions, which are kernel-checked and add no axiom, so each must rest on standard
kernel principles and no others. Two of them use `Classical.byContradiction` to read
a membership out of its absence, which is where `Classical.choice` comes in; the
rest take the excluded middle not at all. These are asserted rather than printed:
each `#guard_msgs` pins the message `#print axioms` emits, so a proof that acquires
any axiom fails the build instead of printing a longer list for a reader to notice.
Whitespace is compared loosely, so what is pinned is the names, not the line breaks
they happen to wrap at. -/

/--
info: 'Scidonia.FracPerm.StateVar.Run.writeStep_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms writeStep_spec

/--
info: 'Scidonia.FracPerm.StateVar.Run.writeStep_lands' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms writeStep_lands

/--
info: 'Scidonia.FracPerm.StateVar.Run.every_write_step_keeps_its_address' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms every_write_step_keeps_its_address

/--
info: 'Scidonia.FracPerm.StateVar.Run.writeStep_check' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms writeStep_check

/--
info: 'Scidonia.FracPerm.StateVar.Run.writeStep_resolve' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms writeStep_resolve

/--
info: 'Scidonia.FracPerm.StateVar.Run.run_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms run_accept

/--
info: 'Scidonia.FracPerm.StateVar.Run.exclusive_head' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exclusive_head

/--
info: 'Scidonia.FracPerm.StateVar.Run.takeOut_counted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms takeOut_counted

/--
info: 'Scidonia.FracPerm.StateVar.Run.plug_counted' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms plug_counted

/--
info: 'Scidonia.FracPerm.StateVar.Run.CHeap.count_writeSlots' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CHeap.count_writeSlots

/--
info: 'Scidonia.FracPerm.StateVar.Run.pair_handle_held_copies' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pair_handle_held_copies

/--
info: 'Scidonia.FracPerm.StateVar.Run.pair_handle_dropped_keeps' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pair_handle_dropped_keeps

/--
info: 'Scidonia.FracPerm.StateVar.Run.writeStep' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms writeStep

/--
info: 'Scidonia.FracPerm.StateVar.Run.resolve' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms resolve

/--
info: 'Scidonia.FracPerm.StateVar.Run.writeStep_leaf_count' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms writeStep_leaf_count

/--
info: 'ScidoniaTest.Run.counted_of' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counted_of

/--
info: 'ScidoniaTest.Run.chain_accept' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chain_accept

/--
info: 'ScidoniaTest.Run.chain_writeStep_lands' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chain_writeStep_lands

/--
info: 'ScidoniaTest.Run.pair_held_copies' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pair_held_copies

/--
info: 'ScidoniaTest.Run.pair_dropped_keeps' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pair_dropped_keeps

/--
info: 'ScidoniaTest.Run.pairCarrying_branches' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pairCarrying_branches

/--
info: 'ScidoniaTest.Run.prog_run' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prog_run

/--
info: 'ScidoniaTest.Run.prog_run_write_keeps_the_address' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prog_run_write_keeps_the_address


end ScidoniaTest.Run
