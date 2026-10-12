/-
Checks for `Scidonia.RC.Target` and `Scidonia.RC.Ownership`.

The two modules are the target runtime of λ¹'s heap semantics at
`Scidonia.FracPerm.StateVar.RCHeap`'s counted heap, and the ownership account of it:
the coupling invariant `Couple`, its preservation by every step, and the two store
theorems. A proof development has no pre-fix behaviour to observe, so the checks here
meet its definitions and theorems from outside, on heaps, terms and multiplicities a
client can build. They are of six kinds:

* **The checks and the store's branch, evaluated**, as `#guard`s: the liveness test at
  the cells of a small heap, the write's own check at two operands, the value
  realization's shape test, and the addressed cell's count. Each detector has an
  affirmative control beside it — a false equation of the same `#guard` shape whose
  message is pinned — so a guard is shown to fire rather than to pass whatever it is
  given.
* **The runs, evaluated**, as `#guard`s of the configurations the evaluator reaches:
  the store at a cell of count one, whose cell keeps its location and holds the
  written slots there and whose emptied slot's cell the write's cascade frees; the
  store at a cell of count two, whose written slots land at the heap's fresh location;
  and a lowered term of `Scidonia.RC.Lower` run on a small counted heap, from a
  configuration that satisfies the coupling invariant through every step to the write.
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
  well formed, counted at the run's handles and the term's own references, and the
  multiplicities' variables are bound.
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

/-- The multiplicities' variable is bound in the environment. -/
theorem one_bound : Bound env0 one := by
  intro p hp
  have hp' : p = (0, 0) := by simpa [one] using hp
  rw [hp']
  exact ⟨0, by decide⟩

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

/-- The shared multiplicities' variable is bound in the environment. -/
theorem two_bound : Bound env0 two := by
  intro p hp
  have hp' : p = (0, 0) := by simpa [two] using hp
  rw [hp']
  exact ⟨0, by decide⟩

/-- The shared configuration satisfies the coupling invariant. -/
theorem shared_couple : Couple shared [] env0 two :=
  ⟨shared_wf, shared_counted, two_bound⟩

/-! ## The checks, the branch and the runs, evaluated

Every `#guard` below is answered by an affirmative control: a false equation of the
same shape whose reported message is pinned, so the guard is shown to fire and not to
pass whatever it is given. -/

/-
The liveness test finds the cells the heaps list and nothing else, and the value
realization's shape test separates a variable from an allocated value.
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

#guard decide (allocB (.var 2) = false && allocB (.con2 7 (.var 1) (.var 2)) = true)

/--
error: Expression
  decide (allocB (Expr.var 2) = true)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (allocB (.var 2) = true)

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
The shared store runs and copies: the written slots are read back at the fresh
location `3`, the old cell keeps its slots and one reference fewer, and the
configuration the step leaves is the one the rule gives — the fresh location in the
term's own multiplicity, where the update's handle list had it.
-/
#guard decide ((update shared [0, 0] 0 [2, 2]).1.lookup (fresh shared [2, 2]) = some [2, 2])
#guard decide ((update shared [0, 0] 0 [2, 2]).1.lookup 0 = some [1, 2])
#guard decide ((update shared [0, 0] 0 [2, 2]).1.count 0 = 1)
#guard decide (trun 1 (shared, [], env0, two, storeTerm)
  = (sharedAfter, [], env0.set 0 3, Multi.insert (Multi.dropFirst two 0) 0 3, .var 0))

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
    (r := 0) (ks := [2, 2]) owned_couple (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- The store theorems applied at the owned configuration: the store's branch is one, so
`store_owned_is_destructive` reads the cell's location back with the written slots. -/
theorem owned_store_applied :
    (update owned [0] 0 [2, 2]).1.lookup 0 = some [2, 2] :=
  store_owned_is_destructive (c := owned) (hs := []) (ρ := env0) (m := one) (y := 0)
    (r := 0) (ks := [2, 2]) owned_couple (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- The store theorems applied at the shared configuration: the subject is held twice,
so `store_shared_copies` reads the written slots back at the heap's fresh location, the
old cell's slots, and its count one lower. -/
theorem shared_store_applied :
    (update shared [0, 0] 0 [2, 2]).1.lookup (fresh shared [2, 2]) = some [2, 2]
      ∧ (update shared [0, 0] 0 [2, 2]).1.lookup 0 = CHeap.lookup shared 0
      ∧ (update shared [0, 0] 0 [2, 2]).1.count 0 = CHeap.count shared 0 - 1 :=
  store_shared_copies (c := shared) (hs := []) (ρ := env0) (m := two) (y := 0) (r := 0)
    (ks := [2, 2]) shared_couple (by decide) (by decide) (by decide) (by decide)

/-- The per-step theorem at the owned configuration: the step the store's rule takes
leaves a coupled configuration, at the multiplicity and in the environment it leaves. -/
theorem owned_step_couple :
    Couple (update owned [0] 0 [2, 2]).1 [] env0 one :=
  couple_step (c := owned) (hs := []) (ρ := env0) (m := one)
    (e := storeTerm) (c' := (update owned [0] 0 [2, 2]).1) (hs' := []) (ρ' := env0)
    (m' := one) (e' := .var 0)
    (TStep.storeExclusive (by decide) (ValRef.var (by decide) (by decide)) (by decide)
      (by decide) (by decide))
    owned_couple

/-- The per-step theorem at the shared configuration: the copying store's step leaves a
coupled configuration, with the subject bound to the fresh location. -/
theorem shared_step_couple :
    Couple (update shared [0, 0] 0 [2, 2]).1 []
      (env0.set 0 (fresh shared [2, 2]))
      (Multi.insert (Multi.dropFirst two 0) 0 (fresh shared [2, 2])) :=
  couple_step (c := shared) (hs := []) (ρ := env0) (m := two)
    (e := storeTerm) (c' := (update shared [0, 0] 0 [2, 2]).1) (hs' := [])
    (ρ' := env0.set 0 (fresh shared [2, 2]))
    (m' := Multi.insert (Multi.dropFirst two 0) 0 (fresh shared [2, 2])) (e' := .var 0)
    (TStep.storeShared (by decide) (ValRef.var (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide))
    shared_couple

/-- The two steps of the lowered run that move the multiplicity are the instructions'
own: the `dup` takes the term's multiplicity of the second variable's reference from
one to two, and the `drop` takes the first variable's from one to none. -/
theorem lowered_multiplicity :
    (expand (Multi.insert [(0, 0), (1, 1), (2, 2)] 2 2)).count 2 = 2
      ∧ (expand (Multi.dropFirst [(0, 0), (1, 1), (2, 2)] 0)).count 0 = 0 := by
  decide

/-- The `dup` and `drop` multiplicity theorems at those references. -/
theorem multiplicity_moves :
    Multi.weight (Multi.insert [(0, 0), (1, 1)] 2 2) 2 = Multi.weight [(0, 0), (1, 1)] 2 + 1
      ∧ (expand (Multi.dropFirst [(0, 0), (1, 1), (2, 2)] 0)).count 0 + 1
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
