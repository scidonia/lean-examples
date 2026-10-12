/-
Checks for `Scidonia.RC.Target` and `Scidonia.RC.Ownership`.

The two modules are the target runtime of λ¹'s heap semantics at
`Scidonia.FracPerm.StateVar.RCHeap`'s counted heap, and the ownership account of it:
the coupling invariant `Couple`, its preservation by every step, and the two store
theorems. A proof development has no pre-fix behaviour to observe, so the checks here
meet its definitions and theorems from outside, on heaps, terms and multiplicities a
client can build. They are of seven kinds:

* **The checks and the store's branch, evaluated**, as `#guard`s: the liveness test at
  the cells of a small heap, the write's own check at two operands, the naming checks
  the rebinding instructions make (`freeName`, `nameOnly`, `nameGone`), and the
  addressed cell's count. Each detector has an affirmative control beside it — a false
  equation of the same `#guard` shape whose message is pinned — so a guard is shown to
  fire rather than to pass whatever it is given.
* **The term's own account, refused**, as theorems: the mis-tagged pair the coupling
  invariant and the account relation both refuse, and the affirmative counterpart of
  each — the same pair tagged at the reference its variable names is one the account
  holds.
* **The runs, evaluated**, as `#guard`s of the configurations the evaluator reaches:
  the store at a cell of count one, whose cell keeps its location and holds the
  written slots there and whose emptied slot's cell the write's cascade frees; the
  store at a cell of count two, whose written slots land at the heap's fresh location;
  and a lowered term of `Scidonia.RC.Lower` run on a small counted heap, from a
  configuration that satisfies the coupling invariant through every step to the write.
* **The evaluation contexts, evaluated**, as `#guard`s of the configurations the
  evaluator reaches in the positions λ¹'s heap semantics reaches: a binding whose
  right-hand side is a computation, an application whose function is one, an
  application whose argument is one while the function is a value, and the two fields
  of a node construction.
* **The countermodel and its affirmative control**, as theorems about concrete
  configurations: at one heap and one term, the store at a multiplicity of two copies
  — the written slots land at a fresh location and the old cell keeps its slots and
  loses a reference — while the same store after the term's extra occurrence is
  released is destructive and keeps the cell's location.
* **The store theorems, applied**, at those very configurations: the owned store's
  location is the one `store_owned_is_destructive` gives, and the copying store's
  fresh location, kept slots and lost reference are the three `store_shared_copies`
  gives.
* **The coupling invariant at those configurations**, read from outside: the heaps are
  well formed, counted at the run's handles and the term's own references, and each
  pair of the account names the reference the environment binds its variable to; the
  steps the contexts take leave coupled configurations.
* **Axioms**: each representative theorem's `#print axioms` output is pinned to the
  standard kernel principles, so a proof that acquires any other axiom fails the build
  rather than printing a longer list for a reader to notice.

The heaps below are read as exactly the cells they list, which is the reading
`Counted` is stated under; nothing here constructs a heap from a compiled run.
-/
import Scidonia.RC

open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap
open Scidonia.RC

namespace ScidoniaTest.Target

/-
The default instance-search budget is not enough to compare a configuration's five
components under `Option`, which is the shape a step's answer has: the product
instance's search for `DecidableEq` grows past it.
-/
set_option synthInstance.maxSize 400

/-! ## The heaps and configurations the checks are read at -/

/-- A heap of three unnamed cells: the reference `0` is the one the term's
multiplicity names, and `1` and `2` are the ones the cell at hand's slots name. -/
def base : CHeap :=
  [(0, { slots := [], count := 1 }), (1, { slots := [], count := 1 }),
    (2, { slots := [], count := 1 })]

/-- The same heap with the cell at `0` carrying two slots: the cell the two stores
write, whose slot `0` names `1` and whose slot `1` names `2`. -/
def owned : CHeap :=
  [(0, { slots := [1, 2], count := 1 }), (1, { slots := [], count := 1 }),
    (2, { slots := [], count := 1 })]

/-- The heap a destructive store of `[2, 2]` into the cell at `0` leaves: that cell
holds the written slots, and the cell its emptied slot named is freed by the write's
cascade. -/
def ownedAfter : CHeap :=
  [(0, { slots := [2, 2], count := 1 }), (2, { slots := [], count := 2 })]

/-- The heap the owned store is read at, with the cell at `0` named twice by the
term's own references: the same cells as `owned` with the count the second occurrence
gives. -/
def shared : CHeap :=
  [(0, { slots := [1, 2], count := 2 }), (1, { slots := [], count := 1 }),
    (2, { slots := [], count := 1 })]

/-- The heap a copying store of `[2, 2]` into the cell at `0` leaves: the written
slots land at the fresh location `3`, the old cell keeps its slots and loses a
reference, and the cells the written slots name have their counts raised by the new
cell's occurrences. -/
def sharedAfter : CHeap :=
  [(3, { slots := [2, 2], count := 1 }), (0, { slots := [1, 2], count := 1 }),
    (1, { slots := [], count := 1 }), (2, { slots := [], count := 3 })]

/-- A heap whose cell at `0` a heap slot also names: the cell at `1` holds a slot naming
it, so the subject's cell is at a count of two while the term holds its occurrence
once. -/
def sharedBySlot : CHeap :=
  [(0, { slots := [1, 2], count := 2 }), (1, { slots := [0], count := 1 }),
    (2, { slots := [], count := 1 })]

/-- The environment the checks read: the variable `0` names the cell at `0` — the
store's subject — and `1` and `2` name the cells of the same name. -/
def env0 : TEnv := [(0, 0), (1, 1), (2, 2)]

/-- The term's own references at the owned configurations: one occurrence of the
variable `0`, the store's subject. -/
def one : Multi := [(0, 0)]

/-- The term's own references at the shared configuration: two occurrences of the
variable `0`, so the subject is named twice and an update below it copies. -/
def two : Multi := [(0, 0), (0, 0)]

/-- The store the checks read: slot `0` of the cell the subject names is set to the
reference the variable `2` names. -/
def storeTerm : Expr := .store (.var 0) 0 (.var 2)

/-- The same store behind the release of the term's own occurrence of the subject,
which is the sequence the discipline's take-out performs before the write. -/
def dropStoreTerm : Expr := .drop 0 (.store (.var 0) 0 (.var 2))

/-- A binding whose right-hand side is a computation: the right-hand side duplicates
the subject's occurrence before the binding reads it. -/
def rhsTerm : Expr := .bind 1 (.dup 0 (.var 0)) (.var 1)

/-- An application whose function is a computation: the function position holds the
duplication before the application reads its argument. -/
def funStepTerm : Expr := .app (.dup 0 (.var 0)) (.var 1)

/-- An application whose argument is a computation and whose function is not:
`(λ1. 1) (dup 0; 0)`. -/
def argStepTerm : Expr := .app (.lam 1 (.var 1)) (.dup 0 (.var 0))

/-- A node construction whose field is a computation. -/
def conStepTerm : Expr := .con1 7 (.dup 0 (.var 0))

/-- A binary node construction whose first field is a computation. -/
def conStepTwoTerm : Expr := .con2 7 (.dup 0 (.var 0)) (.var 1)

/-- A binary node construction whose second field is a computation and whose first is
a value. -/
def conStepRightTerm : Expr := .con2 7 (.var 1) (.dup 0 (.var 0))

/-! ## The term's own account, refused

The pair the coupling invariant and the account relation both refuse is the mis-tagged
one: a pair that stores the reference `0` under the tag `1`. The environment names `1`
at `1`, so neither `Bound` nor the store's account holds it, and each refusal has its
affirmative counterpart beside it — the pair tagged at the reference its variable
names, which the account does hold. These are theorems rather than pinned failures:
the statements are decidable predicates a client can ask about, so a theorem is what
this repository's idiom gives. -/

/-- The mis-tagged pair is refused by the coupling invariant: `env0.lookup 1` is
`some 1`, and the pair stores `0`. -/
theorem mistagged_bound_refused : ¬ Bound env0 [(1, 0)] := by
  intro h
  exact absurd (h (1, 0) (by simp)) (by decide)

/-- The pair tagged at the reference its variable names is one the invariant holds:
the affirmative counterpart of the refusal beside it. -/
theorem tagged_bound_holds : Bound env0 [(1, 1)] := by
  intro p hp
  have hp' : p = (1, 1) := by simpa using hp
  rw [hp']
  decide

/-- The mis-tagged pair is refused by the term's own account of the store: the
account holds no pair tagged `0` at all. -/
theorem mistagged_owns_refused : ¬ Owns env0 [(1, 0)] storeTerm := by
  intro h
  obtain ⟨_, _, hmem⟩ := h.store_occurrence
  simp at hmem

/-- The term's own account of the store holds the subject's pair at the reference
`env0` names for it: the affirmative counterpart of the refusal beside it. -/
theorem owned_owns_holds : Owns env0 one storeTerm :=
  Owns.store (r := 0) (by decide) (by decide)

/-- The term's own account at the shared configuration holds the subject's pair at the
reference `env0` names for it, which is the account that configuration carries. -/
theorem two_owns_holds : Owns env0 two storeTerm :=
  Owns.store (r := 0) (by decide) (by decide)

/-- The account's reading of the release the take-out performs: the `drop` reads the
occurrence it releases out of the term's own account. -/
theorem drop_owns_holds : Owns env0 two dropStoreTerm :=
  Owns.drop (r := 0) (by decide) (by decide)

/-- The account's reading of a binding of a variable: the bound variable's occurrence
is the one the account holds, and the binder's name is one the account holds nowhere
but at that occurrence's reference. -/
theorem bind_owns_holds : Owns env0 one (.bind 1 (.var 0) (.var 1)) :=
  Owns.bindVar (r := 0) (by decide) (by decide)
    (by intro p hp; simp [one] at hp; rw [hp]; decide)

/-- The account's reading of an application to a variable: the argument's occurrence is
one the account holds. -/
theorem app_owns_holds : Owns env0 one (.app (.lam 1 (.var 1)) (.var 0)) :=
  Owns.appVar (r := 0) (by decide) (by decide)
    (by intro p hp; simp [one] at hp; rw [hp]; decide)

/-! ## Counting the small heaps

`Counted` is a statement about every reference, so a small heap is counted by hand:
its cells' counts are read off the occurrences and the hands, and the heaps here are
closed — every slot names a cell they list and every reference the term holds names
one — which is what lets a reference the heap does not list be discharged. -/

/-- A heap is counted when every cell it lists carries the count its occurrences and
its hands give it, every slot names a cell it lists, and every reference the term
holds names one. These are the three conditions a reader can check at a small
heap. -/
theorem counted_of (c : CHeap) (hs : List Ref)
    (hcount : ∀ x ∈ CHeap.refs c, CHeap.count c x = (CHeap.slots c).count x + hs.count x)
    (hslot : ∀ x ∈ CHeap.slots c, x ∈ CHeap.refs c)
    (hhandle : ∀ x ∈ hs, x ∈ CHeap.refs c) : Counted c hs := by
  rw [counted_iff_slots]
  intro x
  by_cases hx : x ∈ CHeap.refs c
  · exact hcount x hx
  · have hs0 : (CHeap.slots c).count x = 0 :=
      List.count_eq_zero.mpr (fun hmem => hx (hslot x hmem))
    have hh0 : hs.count x = 0 :=
      List.count_eq_zero.mpr (fun hmem => hx (hhandle x hmem))
    rw [CHeap.count_eq_zero_of_not_mem hx, hs0, hh0]

/-- The base heap is counted at the term's three own references. -/
theorem base_counted : Counted base [0, 1, 2] := by
  refine counted_of base [0, 1, 2] ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by simpa [base] using hx
    rcases hx' with rfl | rfl | rfl <;> decide
  · intro x hx; simp [base] at hx
  · intro x hx
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by simpa using hx
    rcases hx' with rfl | rfl | rfl <;> decide

/-- The base heap is one the store's rules are stated about. -/
theorem base_wf : CHeap.WF base := by rw [CHeap.WF]; decide

/-- The owned heap is counted at the term's one own reference and the slots of the
cell at `0`. -/
theorem owned_counted : Counted owned ([] ++ expand one) := by
  refine counted_of owned [0] ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by simpa [owned] using hx
    rcases hx' with rfl | rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 1 ∨ x = 2 := by simpa [owned] using hx
    rcases hx' with rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 0 := by simpa using hx
    rw [hx']; decide

/-- The owned heap is well formed. -/
theorem owned_wf : CHeap.WF owned := by rw [CHeap.WF]; decide

/-- The owned heap carries no counted-zero cell. -/
theorem owned_live : CHeap.Live owned := by rw [CHeap.Live]; decide

/-- The multiplicities' variable is bound in the environment, at the reference it
names. -/
theorem one_bound : Bound env0 one := by
  intro p hp
  have hp' : p = (0, 0) := by simpa [one] using hp
  rw [hp']
  decide

/-- The owned configuration satisfies the coupling invariant: the heap is well formed,
its counts are `Counted`'s at the run's handles and the term's own references, and the
multiplicity's variable is bound. -/
theorem owned_couple : Couple owned [] env0 one :=
  ⟨owned_wf, owned_counted, one_bound⟩

/-- The shared heap is counted at the term's two own references and the slots of the
cell at `0`. -/
theorem shared_counted : Counted shared ([] ++ expand two) := by
  refine counted_of shared [0, 0] ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by simpa [shared] using hx
    rcases hx' with rfl | rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 1 ∨ x = 2 := by simpa [shared] using hx
    rcases hx' with rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 0 := by simpa using hx
    rw [hx']; decide

/-- The shared heap is well formed. -/
theorem shared_wf : CHeap.WF shared := by rw [CHeap.WF]; decide

/-- The shared multiplicities' variable is bound in the environment, at the reference
it names. -/
theorem two_bound : Bound env0 two := by
  intro p hp
  have hp' : p = (0, 0) := by simpa [two] using hp
  rw [hp']
  decide

/-- The shared configuration satisfies the coupling invariant. -/
theorem shared_couple : Couple shared [] env0 two :=
  ⟨shared_wf, shared_counted, two_bound⟩

/-- The heap a heap slot shares is counted at the term's one own reference. -/
theorem sharedBySlot_counted : Counted sharedBySlot ([] ++ expand one) := by
  refine counted_of sharedBySlot [0] ?_ ?_ ?_
  · intro x hx
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by simpa [sharedBySlot] using hx
    rcases hx' with rfl | rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 1 ∨ x = 2 ∨ x = 0 := by simpa [sharedBySlot] using hx
    rcases hx' with rfl | rfl | rfl <;> decide
  · intro x hx
    have hx' : x = 0 := by simpa using hx
    rw [hx']; decide

/-- The heap a heap slot shares is well formed. -/
theorem sharedBySlot_wf : CHeap.WF sharedBySlot := by rw [CHeap.WF]; decide

/-- The configuration whose cell a heap slot also names satisfies the coupling
invariant: the term holds the subject's occurrence once while another cell's slot
names the cell. -/
theorem sharedBySlot_couple : Couple sharedBySlot [] env0 one :=
  ⟨sharedBySlot_wf, sharedBySlot_counted, one_bound⟩

/-! ## The checks, the branch and the runs, evaluated

Every `#guard` below is answered by an affirmative control: a false equation of the
same shape whose reported message is pinned, so the guard is shown to fire and not to
pass whatever it is given. -/

/-
The liveness test finds the cells the heaps list and nothing else, and the naming
checks separate an account that holds a name from one that does not: `one` holds the
variable `0` and nothing else, and the copying store's check is the one the account
makes once the consumed occurrence has left it.
-/
#guard decide (live owned 2 && live shared 2)
#guard decide (live owned 9 = false)

/--
error: Expression
  decide (live owned 9 = true)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (live owned 9 = true)

#guard decide (freeName one 1 && freeName one 2 && freeName one 0 = false)
#guard decide (nameOnly two 0 0 && nameOnly two 0 9 = false)
#guard decide (nameGone one 0 0 && nameGone two 0 0 = false)

/--
error: Expression
  decide (freeName one 0 = true)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (freeName one 0 = true)

/--
error: Expression
  decide (nameGone two 0 0 = true)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (nameGone two 0 0 = true)

/-
The write's own check passes at an operand that names live cells and neither the cell
it writes nor one of that cell's own slots, and turns away an operand that names the
cell it writes or a reference the heap does not list.
-/
#guard decide (writeCheck owned 0 [2, 2])
#guard decide (writeCheck owned 0 [0] = false && writeCheck owned 0 [9] = false)

/--
error: Expression
  decide (writeCheck owned 0 [0] = true)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (writeCheck owned 0 [0] = true)

/-
The store's branch is the heap's own count: one at the owned configuration and two at
the shared one, and that is what makes the same term destructive at the one and
copying at the other.
-/
#guard decide (CHeap.count owned 0 = 1 && CHeap.count shared 0 = 2)

/--
error: Expression
  decide (owned.count 0 = 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (CHeap.count owned 0 = 2)

/-
The owned store runs: its cell keeps its location and holds the written slots there,
the emptied slot's cell is freed by the write's cascade, and the configuration the
step leaves is the one the rule gives.
-/
#guard decide (ownedAfter.lookup 0 = some [2, 2])
#guard decide (CHeap.count ownedAfter 1 = 0 && 1 ∉ CHeap.refs ownedAfter)
#guard decide (trun 1 (owned, [], env0, one, storeTerm) = (ownedAfter, [], env0, one, .var 0))

/--
error: Expression
  decide (trun 1 (owned, [], env0, one, storeTerm) = (owned, [], env0, one, Expr.var 0))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (trun 1 (owned, [], env0, one, storeTerm) = (owned, [], env0, one, .var 0))

/-
The shared store copies: the written slots are read back at the fresh location `3`,
the old cell keeps its slots and one reference fewer, and the update's count at the
fresh location is the one the rule gives. The store's *step* is not taken at the
two-occurrence configuration itself: its copying branch reads the subject's name at
the fresh location from then on, so the rule requires the account to hold no other
occurrence of the name, which is what the release below leaves.
-/
#guard decide ((update shared [0, 0] 0 [2, 2]).1.lookup (fresh shared [2, 2]) = some [2, 2])
#guard decide ((update shared [0, 0] 0 [2, 2]).1.lookup 0 = some [1, 2])
#guard decide ((update shared [0, 0] 0 [2, 2]).1.count 0 = 1)
#guard decide (trun 1 (shared, [], env0, two, storeTerm) = (shared, [], env0, two, storeTerm))

/--
error: Expression
  decide
    (trun 1 (shared, [], env0, two, storeTerm) =
      (sharedAfter, [], env0.set 0 3, (two.dropOcc 0 0).insert 0 3, Expr.var 0))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (trun 1 (shared, [], env0, two, storeTerm)
  = (sharedAfter, [], env0.set 0 3, Multi.insert (Multi.dropOcc two 0 0) 0 3, .var 0))

/--
error: Expression
  decide ((update shared [0, 0] 0 [2, 2]).fst.lookup 3 = some [1, 2])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((update shared [0, 0] 0 [2, 2]).1.lookup 3 = some [1, 2])

/-
The release of the term's one extra occurrence, and the same store after it: the
release's decrement lands at the same cells as the owned configuration's heap, so the
same term is destructive there.
-/
#guard decide ((decRef shared [] 0).1 = owned)
#guard decide (trun 2 (shared, [], env0, two, dropStoreTerm)
  = (ownedAfter, [], env0, one, .var 0))

/--
error: Expression
  decide ((decRef shared [] 0).fst = shared)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((decRef shared [] 0).1 = shared)

/-
The copying store's step at the configuration a heap slot shares: the subject's cell
is at a count of two while the term holds its occurrence once, so the store runs, its
written slots land at the fresh location, and the subject names it.
-/
#guard decide (trun 1 (sharedBySlot, [], env0, one, storeTerm)
  = ((update sharedBySlot [0] 0 [2, 2]).1, [], env0.set 0 (fresh sharedBySlot [2, 2]),
     Multi.insert (Multi.dropOcc one 0 0) 0 (fresh sharedBySlot [2, 2]), .var 0))

/--
error: Expression
  decide (tstep? sharedBySlot [] env0 one storeTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (tstep? sharedBySlot [] env0 one storeTerm = none)

/-! ## A lowered term, evaluated

The lowering of `Scidonia.RC.Lower` is read back at a small source term and the term
it answers is run on a small counted heap: the prologue's `dup` and `drop`, the
binding that allocates the two-slot node, and the store at the cell it bound. -/

/-- The source term the lowering is read at: the variable `0` is bound to a two-slot
node over the variables `1` and `2`, and its slot `0` is then set to the reference
`2` names. -/
def source : Expr := .bind 0 (.con2 7 (.var 1) (.var 2)) (.store (.var 0) 0 (.var 2))

/-- The lowering of the source term under the owned occurrences `[0, 1, 2]`: the
prologue supplies the second use of `2` and releases the unused occurrence of `0`. -/
def lowered : Expr :=
  .dup 2 (.drop 0 (.bind 0 (.con2 7 (.var 1) (.var 2)) (.store (.var 0) 0 (.var 2))))

/-
The lowering answers the term above, and the prologue it inserts is the two
instructions the differential demands.
-/
#guard decide (lowerB [] [0, 1, 2] source = some lowered)
#guard decide (lowerB [] [0, 1, 2] source
  = some (.dup 2 (.drop 0 (.bind 0 (.con2 7 (.var 1) (.var 2)) (.store (.var 0) 0 (.var 2))))))

/--
error: Expression
  decide (lowerB [] [0, 1, 2] source = some source)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (lowerB [] [0, 1, 2] source = some source)

/-
The lowered term runs on the base heap from a configuration that satisfies the
coupling invariant: the `dup` raises the second variable's cell, the `drop` releases
the term's occurrence of `0` and frees that cell, the binding allocates the node at
the heap's fresh location `3` and the binder takes up the handle the allocation handed
out, and the store lands the written slots at the bound cell.

The heap the run leaves: the node at `3` holds the written slots `[2, 2]`, the cell
its emptied slot named is freed by the write's cascade, and the cells the written
slots name carry the counts the new cell's occurrences give them.
-/
#guard decide (trun 4 (base, [], env0, [(0, 0), (1, 1), (2, 2)], lowered)
  = ([(3, { slots := [2, 2], count := 1 }), (1, { slots := [], count := 1 }),
      (2, { slots := [], count := 4 })],
     [], env0.set 0 3, [(0, 3), (2, 2), (1, 1), (2, 2)], .var 0))

/--
error: Expression
  decide (trun 4 (base, [], env0, [(0, 0), (1, 1), (2, 2)], lowered)
    = (base, [], env0, [(0, 0), (1, 1), (2, 2)], lowered))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (trun 4 (base, [], env0, [(0, 0), (1, 1), (2, 2)], lowered)
  = (base, [], env0, [(0, 0), (1, 1), (2, 2)], lowered))

/-! ## The evaluation contexts, evaluated

The positions λ¹'s heap semantics reaches: a binding's right-hand side, an
application's function and argument, and the fields of a node construction. Each guard
reads the configuration the evaluator answers in that position — the position's step
is the one it takes — and each stands beside a control claiming the configuration took
no step, which the guard beside it shows to fire. -/

/-
A binding whose right-hand side is a computation: the `dup` is the step, taken in the
right-hand side's position, and the binding is left as it was.
-/
#guard decide (tstep? owned [] env0 one rhsTerm
  = some ((dup owned [] 0).1, ([] : List Ref), env0, Multi.insert one 0 0, .bind 1 (.var 0) (.var 1)))

/--
error: Expression
  decide (tstep? owned [] env0 one rhsTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (tstep? owned [] env0 one rhsTerm = none)

/-
An application whose function is a computation: the `dup` is the step, taken in the
function position.
-/
#guard decide (tstep? owned [] env0 one funStepTerm
  = some ((dup owned [] 0).1, ([] : List Ref), env0, Multi.insert one 0 0, .app (.var 0) (.var 1)))

/--
error: Expression
  decide (tstep? owned [] env0 one funStepTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (tstep? owned [] env0 one funStepTerm = none)

/-
An application whose argument is a computation and whose function is a value: the
function's own rule does not apply, and the step taken is the argument's.
-/
#guard decide (tstep? owned [] env0 one argStepTerm
  = some ((dup owned [] 0).1, ([] : List Ref), env0, Multi.insert one 0 0, .app (.lam 1 (.var 1)) (.var 0)))

/--
error: Expression
  decide (tstep? owned [] env0 one argStepTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (tstep? owned [] env0 one argStepTerm = none)

/-
A node construction whose field is a computation: the `dup` is the step, taken in the
field's position, in the unary and in both fields of the binary form.
-/
#guard decide (tstep? owned [] env0 one conStepTerm
  = some ((dup owned [] 0).1, ([] : List Ref), env0, Multi.insert one 0 0, .con1 7 (.var 0)))
#guard decide (tstep? owned [] env0 one conStepTwoTerm
  = some ((dup owned [] 0).1, ([] : List Ref), env0, Multi.insert one 0 0, .con2 7 (.var 0) (.var 1)))
#guard decide (tstep? owned [] env0 one conStepRightTerm
  = some ((dup owned [] 0).1, ([] : List Ref), env0, Multi.insert one 0 0, .con2 7 (.var 1) (.var 0)))

/--
error: Expression
  decide (tstep? owned [] env0 one conStepTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (tstep? owned [] env0 one conStepTerm = none)

/--
error: Expression
  decide (tstep? owned [] env0 one conStepRightTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (tstep? owned [] env0 one conStepRightTerm = none)

/-! ## The evaluation contexts, as theorems

The steps the guards read back, as facts about the relation: the position's step is a
step of `TStep`, and the configuration it leaves is coupled. -/

/-- The binding whose right-hand side is a computation steps there: the configuration
the evaluator answers is the position's step, a step of the relation. -/
theorem rhs_step :
    TStep owned [] env0 one rhsTerm (dup owned [] 0).1 [] env0 (Multi.insert one 0 0)
      (.bind 1 (.var 0) (.var 1)) :=
  tstep?_sound owned [] env0 one rhsTerm (dup owned [] 0).1 [] env0 (Multi.insert one 0 0)
    (.bind 1 (.var 0) (.var 1)) (by decide)

/-- That step leaves a coupled configuration, read at the invariant it started from:
the congruence rule's case of the per-step theorem. -/
theorem rhs_step_couple :
    Couple (dup owned [] 0).1 [] env0 (Multi.insert one 0 0) :=
  couple_step rhs_step owned_couple

/-- The application whose function is a computation steps there, and its step leaves a
coupled configuration. -/
theorem fun_step_couple :
    Couple (dup owned [] 0).1 [] env0 (Multi.insert one 0 0) :=
  couple_step (tstep?_sound owned [] env0 one funStepTerm (dup owned [] 0).1 [] env0
    (Multi.insert one 0 0) (.app (.var 0) (.var 1)) (by decide)) owned_couple

/-- The application whose argument is a computation steps there, and its step leaves a
coupled configuration. -/
theorem arg_step_couple :
    Couple (dup owned [] 0).1 [] env0 (Multi.insert one 0 0) :=
  couple_step (tstep?_sound owned [] env0 one argStepTerm (dup owned [] 0).1 [] env0
    (Multi.insert one 0 0) (.app (.lam 1 (.var 1)) (.var 0)) (by decide)) owned_couple

/-- The node construction whose field is a computation steps there, and its step leaves
a coupled configuration. -/
theorem con_step_couple :
    Couple (dup owned [] 0).1 [] env0 (Multi.insert one 0 0) :=
  couple_step (tstep?_sound owned [] env0 one conStepTerm (dup owned [] 0).1 [] env0
    (Multi.insert one 0 0) (.con1 7 (.var 0)) (by decide)) owned_couple

/-- The guarded run of the binding whose right-hand side is a computation is a run of
the relation. -/
theorem rhs_run_reached :
    TStepStar owned [] env0 one rhsTerm (trun 1 (owned, [], env0, one, rhsTerm)).1
      (trun 1 (owned, [], env0, one, rhsTerm)).2.1
      (trun 1 (owned, [], env0, one, rhsTerm)).2.2.1
      (trun 1 (owned, [], env0, one, rhsTerm)).2.2.2.1
      (trun 1 (owned, [], env0, one, rhsTerm)).2.2.2.2 :=
  trun_stepStar 1 owned [] env0 one rhsTerm

/-! ## The countermodel and its affirmative control

At one heap and one term, the store's branch is the multiplicity the term carries for
the subject: two occurrences make the cell's count two and the update copies, and one
occurrence — the state the release leaves — makes it one and the update keeps the
cell's location. -/

/-- The countermodel at the shared heap: the subject's cell is at a count of two, it is
not exclusive, and the update below it copies — the written slots land at the heap's
fresh location rather than at the cell's own, and the old cell keeps its slots and
loses a reference. -/
theorem shared_store_copies :
    CHeap.count shared 0 = 2 ∧ ¬ Exclusive (CHeap.presentation shared) [0, 0] 0
      ∧ (update shared [0, 0] 0 [2, 2]).1.lookup (fresh shared [2, 2]) = some [2, 2]
      ∧ (update shared [0, 0] 0 [2, 2]).1.lookup 0 = some [1, 2]
      ∧ (update shared [0, 0] 0 [2, 2]).1.count 0 = CHeap.count shared 0 - 1 := by
  refine ⟨by decide, ?_, by decide, by decide, by decide⟩
  show ¬ (refCount (CHeap.presentation shared) [0, 0] 0 = 1)
  decide

/-- The affirmative control at that heap and term, after the release of the term's one
extra occurrence: the cell holds one, and the same update keeps its location. The
release's decrement is what turns the copying branch back into the destructive
one. -/
theorem shared_store_keeps_after_drop :
    (update (decRef shared [] 0).1 [] 0 [2, 2]).1.lookup 0 = some [2, 2] := by
  rw [show (decRef shared [] 0).1 = owned by decide]
  exact store_owned_is_destructive (c := owned) (hs := []) (ρ := env0) (m := one) (y := 0)
    (r := 0) (i := 0) (v := .var 2) (ks := [2, 2]) owned_couple (by decide) owned_owns_holds
    (by decide) (by decide) (by decide) (by decide)

/-- The store theorems applied at the owned configuration: the store's branch is one, so
`store_owned_is_destructive` reads the cell's location back with the written slots. -/
theorem owned_store_applied :
    (update owned [0] 0 [2, 2]).1.lookup 0 = some [2, 2] :=
  store_owned_is_destructive (c := owned) (hs := []) (ρ := env0) (m := one) (y := 0)
    (r := 0) (i := 0) (v := .var 2) (ks := [2, 2]) owned_couple (by decide) owned_owns_holds
    (by decide) (by decide) (by decide) (by decide)

/-- The store theorems applied at the shared configuration: the subject is held twice,
so `store_shared_copies` reads the written slots back at the heap's fresh location, the
old cell's slots, and its count one lower. -/
theorem shared_store_applied :
    (update shared [0, 0] 0 [2, 2]).1.lookup (fresh shared [2, 2]) = some [2, 2]
      ∧ (update shared [0, 0] 0 [2, 2]).1.lookup 0 = CHeap.lookup shared 0
      ∧ (update shared [0, 0] 0 [2, 2]).1.count 0 = CHeap.count shared 0 - 1 :=
  store_shared_copies (c := shared) (hs := []) (ρ := env0) (m := two) (y := 0) (r := 0)
    (i := 0) (v := .var 2) (ks := [2, 2]) shared_couple (by decide) (two_owns_holds)
    (by decide) (by decide)

/-- The per-step theorem at the owned configuration: the step the store's rule takes
leaves a coupled configuration, at the multiplicity and in the environment it leaves. -/
theorem owned_step_couple :
    Couple (update owned [0] 0 [2, 2]).1 [] env0 one :=
  couple_step (c := owned) (hs := []) (ρ := env0) (m := one)
    (e := storeTerm) (c' := (update owned [0] 0 [2, 2]).1) (hs' := []) (ρ' := env0)
    (m' := one) (e' := .var 0)
    (TStep.storeExclusive (by decide) (ValRef.var (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide))
    owned_couple

/-- The per-step theorem at a configuration whose cell a heap slot also names: the term
holds the subject's occurrence once and the cell is shared by another cell's slot, so
the store's copying branch is taken and the step leaves a coupled configuration, with
the subject bound to the fresh location. -/
theorem shared_step_couple :
    Couple (update sharedBySlot [0] 0 [2, 2]).1 []
      (env0.set 0 (fresh sharedBySlot [2, 2]))
      (Multi.insert (Multi.dropOcc one 0 0) 0 (fresh sharedBySlot [2, 2])) :=
  couple_step (c := sharedBySlot) (hs := []) (ρ := env0) (m := one)
    (e := storeTerm) (c' := (update sharedBySlot [0] 0 [2, 2]).1) (hs' := [])
    (ρ' := env0.set 0 (fresh sharedBySlot [2, 2]))
    (m' := Multi.insert (Multi.dropOcc one 0 0) 0 (fresh sharedBySlot [2, 2]))
    (e' := .var 0)
    (TStep.storeShared (by decide) (ValRef.var (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide))
    sharedBySlot_couple

/-- The two steps of the lowered run that move the multiplicity are the instructions'
own: the `dup` takes the term's multiplicity of the second variable's reference from
one to two, and the `drop` takes the first variable's from one to none. -/
theorem lowered_multiplicity :
    (expand (Multi.insert [(0, 0), (1, 1), (2, 2)] 2 2)).count 2 = 2
      ∧ (expand (Multi.dropOcc [(0, 0), (1, 1), (2, 2)] 0 0)).count 0 = 0 := by
  decide

/-- The `dup` and `drop` multiplicity theorems at those references. -/
theorem multiplicity_moves :
    Multi.weight (Multi.insert [(0, 0), (1, 1)] 2 2) 2 = Multi.weight [(0, 0), (1, 1)] 2 + 1
      ∧ (expand (Multi.dropOcc [(0, 0), (1, 1), (2, 2)] 0 0)).count 0 + 1
        = (expand [(0, 0), (1, 1), (2, 2)]).count 0 :=
  ⟨dup_multiplicity [(0, 0), (1, 1)] 2 2, drop_multiplicity (by decide)⟩

/-- A configuration the evaluator reaches is reached by the step relation, so the
guarded runs above are facts about the reduction. -/
theorem owned_run_reached :
    TStepStar owned [] env0 one storeTerm (trun 1 (owned, [], env0, one, storeTerm)).1
      (trun 1 (owned, [], env0, one, storeTerm)).2.1 (trun 1 (owned, [], env0, one, storeTerm)).2.2.1
      (trun 1 (owned, [], env0, one, storeTerm)).2.2.2.1
      (trun 1 (owned, [], env0, one, storeTerm)).2.2.2.2 :=
  trun_stepStar 1 owned [] env0 one storeTerm

/-! ## Axioms of representative theorems -/

/--
info: 'Scidonia.RC.store_owned_is_destructive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms store_owned_is_destructive

/--
info: 'Scidonia.RC.store_shared_copies' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms store_shared_copies

/--
info: 'Scidonia.RC.couple_step' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms couple_step

/--
info: 'Scidonia.RC.dup_multiplicity' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms dup_multiplicity

/--
info: 'Scidonia.RC.drop_multiplicity' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms drop_multiplicity

/--
info: 'Scidonia.RC.tstep?_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tstep?_sound

/--
info: 'Scidonia.RC.trun_stepStar' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms trun_stepStar

end ScidoniaTest.Target
