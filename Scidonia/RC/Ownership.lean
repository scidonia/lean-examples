/-
The ownership account of the target runtime: what the counts the counted heap keeps
have to do with the term that runs on it, and the two branches of the write read at
a configuration.

`Scidonia.RC.Target` gives the runtime of λ¹'s heap semantics at
`Scidonia.FracPerm.StateVar.RCHeap`'s counted heap. That heap's counts are
`Counted`'s: a cell's count is its slot occurrences plus the handles held outside
the store. A term that runs on the heap holds occurrences of its own — the
references its variables name — and those are names on the same cells, so the counts
have to be stated at the run's handles *together with* the term's own. That
statement is this module's invariant.

**The multiplicities, and the invariant.** A term's multiplicities are one pair per
occurrence it holds: the variable the occurrence was read at and the reference it
names; `expand` projects the references, and it is the references, not the tags,
that `Counted` reads. The invariant `Couple` says three things of a configuration:
the heap is well formed (`CHeap.WF`, which the release's own theorem reads), its
counts are `Counted`'s at the run's handles together with the term's own references,
and the multiplicities' variables are bound in the environment. The first carries
the counted heap's own invariant into the configuration — the same reading `Accept`
in `Scidonia.FracPerm.StateVar.Run` has of `CHeap.Healthy`; the second is the
coupling; the third is what makes the environment part of the statement rather than
a decoration.

**What is proved.** `couple_step` is the per-step theorem: every step of the
relation preserves `Couple`, and each of its cases rests on `RCHeap`'s own theorems
— `counted_dup`'s arithmetic for the increment, `counted_decRef` and
`counted_dealloc_handle` with `counted_cascade` for the two decrements,
`counted_alloc` for the value realization, `counted_writeSlots` with
`counted_cascade` for the destructive branch of the write, and `counted_update_copy`
for its copying branch. `dup_multiplicity` and `drop_multiplicity` state that the
multiplicity moves exactly as the instructions do.

**The two store theorems.** `store_owned_is_destructive` and `store_shared_copies`
are the deliverable: a store whose subject the term holds once, with nothing else
naming the cell, is at a count of one and takes `RCHeap.update`'s destructive branch
— the cell keeps its location and the written slots are read back there — while a
store whose subject the term holds twice, or whose cell a heap slot also names, is
at a count above one and takes the copying branch — the written slots land at a
fresh location and the old cell keeps its slots and loses a reference.

**What the hypotheses are, and where they come from.** A store rule's premises are
the derivation's: the subject variable's reference (`ρ.lookup y = some r`), the
value's realization, the index's being one of the cell's slots, the write's own check
and the count the branch is taken on. What the theorems add is the reading of the
multiplicity — one occurrence of the subject's reference, or two — and two hypotheses
that are *not* derivable in this slice and are named as such: that no cell's slot
names the subject's cell, and that no handle the run holds names it. Those are what
the discipline's take-out provides: on the run-time path the occurrence is taken out
of the array and the pair's handle is dropped before the focus check, so the write
runs with the term's own occurrence the only name left on the cell — `Run.writeStep`'s
schema is exactly that sequence, and its `takeout_pair_count_two` and
`takeout_dropped_count_one` are the nested case's account of it. `CHeap.WF` comes
from the configuration. Nothing here hides a hypothesis: what is not a rule's
premise is stated, and named as an assumption, in the theorems' own hypotheses.

## What is modelled, and what is trusted

The multiplicities are a logical account of the term's own occurrences and not a
machine count: `expand` lists references, and the tags record the variable an
occurrence was read at. A binding of a variable moves the variable's occurrence to
the binder; a binding of an allocated value takes up the handle the realization
handed out; and a copying store rebinds the subject variable to the fresh location
and moves one occurrence of the old reference out of the term's own. The count the
update's own handle-list move would have had is stated as an equality of counts
rather than by moving the run's handles, which is what makes the term's own list the
one place a `drop` and a copying store move counts.

The write's branch is `RCHeap.update`'s, and it is the model of the lowering's
`isExclusiveUnsafe` / `lean_array_uset` decision; that decision itself is inside the
runtime's emitted array-write code and is not a branch of the emitted IR. A location
is a `Ref`, a name in a list, and in-place is a fact of this model and not of any
compiled code. That the compiler lowers this repository's write paths into the shape
modelled here is checked by `ScidoniaTest/IRShape.lean` and otherwise trusted. No
theorem here says anything about a compiled program.
-/
import Scidonia.RC.Target

namespace Scidonia.RC

open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap

/-! ## The coupling invariant -/

/-- The multiplicities' variables are bound in the environment. A pair's tag records
the variable an occurrence was read at, so this is the condition that makes the
environment the account of the multiplicities rather than a separate object. -/
def Bound (ρ : TEnv) (m : Multi) : Prop := ∀ p ∈ m, ∃ r, ρ.lookup p.1 = some r

/-- A multiplicity's pairs are pairs of a list they are in. -/
theorem Bound.of_subset {ρ : TEnv} {m m' : Multi} (h : Bound ρ m')
    (hsub : ∀ p ∈ m, p ∈ m') : Bound ρ m :=
  fun p hp => h p (hsub p hp)

/-- A `dup`'s occurrence is tagged with a variable the environment binds. -/
theorem Bound.insert {ρ : TEnv} {m : Multi} (h : Bound ρ m) {x : Var} {r : Ref}
    (hρ : ρ.lookup x = some r) : Bound ρ (Multi.insert m x r) := by
  intro p hp
  rcases List.mem_cons.mp hp with heq | hmem
  · rw [heq]; exact ⟨r, hρ⟩
  · exact h p hmem

/-- A `drop` leaves pairs the environment still binds. -/
theorem Bound.dropFirst {ρ : TEnv} {m : Multi} (h : Bound ρ m) (r : Ref) :
    Bound ρ (Multi.dropFirst m r) :=
  h.of_subset fun _ hp => mem_dropFirst hp

/-- A binding leaves every pair of the multiplicity bound: a pair tagged with the
binder names the binding, and a pair of another name is read past it. -/
theorem Bound.set {ρ : TEnv} {m : Multi} (h : Bound ρ m) (x : Var) (r : Ref) :
    Bound (TEnv.set ρ x r) m := by
  intro p hp
  by_cases hx : p.1 = x
  · refine ⟨r, ?_⟩
    rw [hx]
    exact TEnv.lookup_set_self ρ x r
  · obtain ⟨s, hs⟩ := h p hp
    exact ⟨s, by rw [TEnv.lookup_set_of_ne (fun hh => hx hh.symm) r, hs]⟩

/-- An arm's binders leave the multiplicity's own pairs bound: the arm rebinds none
of the names they hold, so each pair is read past the binders. -/
theorem Bound.bindAll {ρ : TEnv} {m : Multi} (h : Bound ρ m) {ys : List Var}
    {rs : List Ref} (hfree : ∀ p ∈ m, p.1 ∉ ys) : Bound (TEnv.bindAll ρ ys rs) m := by
  intro p hp
  obtain ⟨s, hs⟩ := h p hp
  exact ⟨s, by rw [TEnv.lookup_bindAll_of_not_mem (hfree p hp), hs]⟩

/-- The coupling invariant: the heap is well formed, its counts are `Counted`'s at
the run's handles together with the term's own references, and the multiplicities'
variables are bound in the environment. -/
def Couple (c : CHeap) (hs : List Ref) (ρ : TEnv) (m : Multi) : Prop :=
  CHeap.WF c ∧ Counted c (hs ++ expand m) ∧ Bound ρ m

/-- A coupled configuration's heap is well formed. -/
theorem Couple.wf {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} (h : Couple c hs ρ m) :
    CHeap.WF c := h.1

/-- A coupled configuration's heap is counted at the run's handles and the term's
own references. -/
theorem Couple.counted {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi}
    (h : Couple c hs ρ m) : Counted c (hs ++ expand m) := h.2.1

/-- A coupled configuration's multiplicities name variables the environment
binds. -/
theorem Couple.bound {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi}
    (h : Couple c hs ρ m) : Bound ρ m := h.2.2

/-! ## The arithmetic of the handle lists

`Counted` is a statement about counts, so a handle list is interchangeable with any
other that counts the same at every reference. The lemmas below are the moves the
instructions make on the term's own references: the occurrence a `dup` adds at its
reference, the one a `drop` removes, and the one a copying store leaves behind while
the fresh location joins the run's handles. -/

/-- `Counted` reads only the handles' counts: two handle lists with the same count
at every reference count a heap alike. -/
theorem counted_of_count_eq {c : CHeap} {hs hs' : List Ref} (h : Counted c hs)
    (hcount : ∀ x, hs'.count x = hs.count x) : Counted c hs' :=
  (counted_iff_slots c hs').mpr fun x => by
    rw [(counted_iff_slots c hs).mp h x, hcount x]

/-- One occurrence of `r` counted the same wherever it sits in a list: the two
readings a copying store's handle list has count alike. -/
theorem count_cons_append_swap (r : Ref) (rest l : List Ref) (x : Ref) :
    (rest ++ r :: l).count x = (r :: (rest ++ l)).count x := by
  rw [List.count_append]
  by_cases hx : x = r
  · subst hx
    rw [List.count_cons_self, List.count_cons_self, List.count_append]
    omega
  · simp only [List.count_cons_of_ne (b := r) (a := x) (fun hh => hx hh.symm)]
    rw [List.count_append]

/-- The handle list a `drop` leaves, read as the configuration carries it: the term's
own occurrence goes and the count at the reference falls by one. -/
theorem count_drop (hs : List Ref) (m : Multi) {r : Ref} (hm : 0 < (expand m).count r)
    (x : Ref) : (hs ++ expand (Multi.dropFirst m r)).count x
      = (dropHandle (hs ++ expand m) r).count x := by
  rw [List.count_append]
  by_cases hx : x = r
  · subst hx
    rw [expand_dropFirst_count_self, dropHandle_count_self, List.count_append]
    omega
  · rw [expand_dropFirst_count_of_ne m (r := x) (r' := r) (fun hh => hx hh.symm),
      dropHandle_count_of_ne hx, List.count_append]

/-- The handle list a copying store leaves, read as the configuration carries it: the
fresh location joins the run's handles and one occurrence of the old reference leaves
the term's own. -/
theorem count_store_copy (hs : List Ref) (m : Multi) (y : Var) {r fr : Ref} (h : fr ≠ r)
    (hm : 0 < (expand m).count r) (x : Ref) :
    (hs ++ expand (Multi.insert (Multi.dropFirst m r) y fr)).count x
      = (fr :: dropHandle (hs ++ expand m) r).count x := by
  have hfr : (expand (Multi.dropFirst m r)).count fr = (expand m).count fr :=
    expand_dropFirst_count_of_ne m (r := fr) (r' := r) h.symm
  rw [expand_insert, List.count_append]
  by_cases hx : x = fr
  · subst hx
    rw [List.count_cons_self, hfr, List.count_cons_self, dropHandle_count_of_ne h,
      List.count_append]
    omega
  · simp only [List.count_cons_of_ne (b := fr) (a := x) (fun hh => hx hh.symm)]
    by_cases hxr : x = r
    · subst hxr
      rw [expand_dropFirst_count_self, dropHandle_count_self, List.count_append]
      omega
    · rw [expand_dropFirst_count_of_ne m (r := x) (r' := r) (fun hh => hxr hh.symm),
        dropHandle_count_of_ne hxr, List.count_append]

/-! ## The value realization

A value's realization allocates a cell for a node or a closure and reads a variable's
reference otherwise; its effect on the term's own multiplicities is nothing, so the
invariant stands at the multiplicity it was handed. -/

/-- Realising a value leaves the invariant standing at the multiplicity it was
handed: the cell an allocation creates is named by the handle `RCHeap.alloc` hands
out, and the counts its slots raise are the term's own references, which is what
`counted_alloc` states. -/
theorem valRef_couple : ∀ (c : CHeap) (hs : List Ref) (ρ : TEnv) (v : Expr) (c' : CHeap)
    (hs' : List Ref) (r : Ref) (m : Multi), ValRef c hs ρ v c' hs' r → Couple c hs ρ m →
      Couple c' hs' ρ m
  | c, hs, _, _, _, _, _, _, ValRef.var h hlive, hc => hc
  | c, hs, _, _, _, _, _, _, ValRef.lam, hc => by
      obtain ⟨hW, hcount, hbound⟩ := hc
      exact ⟨CHeap.wf_alloc hW (fresh_not_mem_refs c []),
        counted_alloc hcount (fresh_not_mem_refs c []) (fresh_not_mem_ks c [])
          (by intro y hy; simp at hy),
        hbound⟩
  | c, hs, _, _, _, _, _, _, ValRef.con0, hc => by
      obtain ⟨hW, hcount, hbound⟩ := hc
      exact ⟨CHeap.wf_alloc hW (fresh_not_mem_refs c []),
        counted_alloc hcount (fresh_not_mem_refs c []) (fresh_not_mem_ks c [])
          (by intro y hy; simp at hy),
        hbound⟩
  | c, hs, ρ, _, _, _, _, m, ValRef.con1 hv hlive, hc => by
      obtain ⟨hW₁, hcount₁, hbound⟩ := valRef_couple c hs ρ _ _ _ _ m hv hc
      refine ⟨CHeap.wf_alloc hW₁ (fresh_not_mem_refs _ [_]), ?_, hbound⟩
      refine counted_alloc hcount₁ (fresh_not_mem_refs _ [_]) (fresh_not_mem_ks _ [_]) ?_
      intro y hy
      rw [List.mem_singleton] at hy
      rw [hy]; exact hlive
  | c, hs, ρ, _, _, _, _, m, ValRef.con2 hv₁ hv₂ hl₁ hl₂, hc => by
      obtain ⟨hW₁, hcount₁, _⟩ := valRef_couple c hs ρ _ _ _ _ m hv₁ hc
      obtain ⟨hW₂, hcount₂, hbound⟩ :=
        valRef_couple _ _ ρ _ _ _ _ m hv₂ ⟨hW₁, hcount₁, hc.bound⟩
      refine ⟨CHeap.wf_alloc hW₂ (fresh_not_mem_refs _ [_, _]), ?_, hbound⟩
      refine counted_alloc hcount₂ (fresh_not_mem_refs _ [_, _]) (fresh_not_mem_ks _ [_, _]) ?_
      intro y hy
      rw [List.mem_cons, List.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hl₁
      · exact hl₂

/-- A realization that allocates hands out the fresh cell's handle as the head of the
handle list it leaves, which is what lets a binding take that cell up in place of the
handle. -/
theorem valRef_handles : ∀ (c : CHeap) (hs : List Ref) (ρ : TEnv) (v : Expr) (c' : CHeap)
    (hs' : List Ref) (r : Ref), ValRef c hs ρ v c' hs' r → (∀ z, v ≠ .var z) →
      ∃ rest, hs' = r :: rest
  | _, _, _, .var z, _, _, _, ValRef.var _ _, halloc => absurd rfl (halloc z)
  | _, _, _, _, _, _, _, ValRef.lam, _ => ⟨_, rfl⟩
  | _, _, _, _, _, _, _, ValRef.con0, _ => ⟨_, rfl⟩
  | _, _, _, _, _, _, _, ValRef.con1 _ _, _ => ⟨_, rfl⟩
  | _, _, _, _, _, _, _, ValRef.con2 _ _ _ _, _ => ⟨_, rfl⟩

/-! ## The per-construct preservation lemmas

One lemma per rule of the step relation. Each reads `RCHeap`'s own theorem for the
operation the rule performs, and the arithmetic of the term's own references is what
moves the counts the term carries. -/

/-- A `dup` step preserves the invariant at the multiplicity it leaves: the heap's
count at the reference rises by one and so does the term's own list, which is
`counted_dup`'s arithmetic read at the configuration's handles. -/
theorem couple_dup {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {r : Ref}
    (hc : Couple c hs ρ m) (hρ : ρ.lookup y = some r) (hlive : r ∈ CHeap.refs c) :
    Couple (CHeap.adjust c r (fun n => n + 1)) hs ρ (Multi.insert m y r) := by
  obtain ⟨hW, hcount, hbound⟩ := hc
  refine ⟨CHeap.wf_dup (handles := hs) hW, ?_, Bound.insert hbound hρ⟩
  refine counted_of_count_eq (h := counted_dup hcount hlive) fun x => ?_
  rw [expand_insert]
  simp only [dup]
  exact count_cons_append_swap r hs (expand m) x

/-- A `drop` at a cell of count two or more preserves the invariant at the multiplicity
it leaves: the runtime's non-final decrement and the term's own list both fall by one
at the reference. -/
theorem couple_drop_shared {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var}
    {r : Ref} (hc : Couple c hs ρ m) (_hρ : ρ.lookup y = some r) (_h2 : 2 ≤ CHeap.count c r)
    (hm : 0 < (expand m).count r) :
    Couple (CHeap.adjust c r (fun n => n - 1)) hs ρ (Multi.dropFirst m r) := by
  obtain ⟨hW, hcount, hbound⟩ := hc
  have hhandle : 1 ≤ (hs ++ expand m).count r := by rw [List.count_append]; omega
  exact ⟨CHeap.wf_decRef (handles := hs) hW,
    counted_of_count_eq (counted_decRef hcount hhandle) (count_drop hs m hm),
    Bound.dropFirst hbound r⟩

/-- A `drop` at a cell of count one preserves the invariant at the multiplicity it
leaves: the runtime's final release frees the cell the term named, and the cascade
drops the references its slots held. -/
theorem couple_drop_final {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var}
    {r : Ref} (hc : Couple c hs ρ m) (_hρ : ρ.lookup y = some r) (h1 : CHeap.count c r = 1)
    (hm : 0 < (expand m).count r) :
    Couple (CHeap.cascade (CHeap.dealloc c r)) hs ρ (Multi.dropFirst m r) := by
  obtain ⟨hW, hcount, hbound⟩ := hc
  have hhandle : 1 ≤ (hs ++ expand m).count r := by rw [List.count_append]; omega
  exact ⟨CHeap.wf_release (handles := hs) hW,
    counted_of_count_eq
      (counted_cascade (CHeap.wf_dealloc hW r) (counted_dealloc_handle hW hcount h1 hhandle))
      (count_drop hs m hm),
    Bound.dropFirst hbound r⟩

/-- A binding of a variable preserves the invariant: the heap and the run's handles
are what they were, and the variable's own occurrence becomes the binder's, so the
counts the term carries are the ones it carried. -/
theorem couple_bindVar {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x z : Var}
    {r : Ref} (hc : Couple c hs ρ m) (hρ : ρ.lookup z = some r)
    (hm : 0 < (expand m).count r) :
    Couple c hs (TEnv.set ρ x r) (Multi.insert (Multi.dropFirst m r) x r) := by
  refine ⟨hc.wf, ?_, Bound.insert (Bound.dropFirst (Bound.set hc.bound x r) r)
    (TEnv.lookup_set_self ρ x r)⟩
  refine counted_of_count_eq (h := hc.counted) fun y => ?_
  rw [expand_insert, List.count_append, List.count_append]
  by_cases hy : y = r
  · subst hy
    rw [List.count_cons_self, expand_dropFirst_count_self]
    omega
  · simp only [List.count_cons_of_ne (b := r) (a := y) (fun hh => hy hh.symm)]
    rw [expand_dropFirst_count_of_ne m (r := y) (r' := r) (fun hh => hy hh.symm)]

/-- A binding of an allocated value preserves the invariant: the realization's handle
is the name of the cell it allocated, and the binder's occurrence takes that name up,
so the handle list falls back to the run's own and the multiplicity gains the binder's
occurrence. -/
theorem couple_bindVal {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x : Var}
    {v : Expr} {c' : CHeap} {hs' : List Ref} {r : Ref} (hv : ValRef c hs ρ v c' hs' r)
    (halloc : ∀ z, v ≠ .var z) (hc : Couple c hs ρ m) :
    Couple c' (dropHandle hs' r) (TEnv.set ρ x r) (Multi.insert m x r) := by
  obtain ⟨hW, hcount, _⟩ := valRef_couple c hs ρ v c' hs' r m hv hc
  obtain ⟨rest, hrest⟩ := valRef_handles c hs ρ v c' hs' r hv halloc
  refine ⟨hW, ?_, Bound.insert (Bound.set hc.bound x r) (TEnv.lookup_set_self ρ x r)⟩
  refine counted_of_count_eq (h := hcount) fun y => ?_
  rw [expand_insert, hrest, dropHandle_cons_self]
  exact count_cons_append_swap r rest (expand m) y

/-- An application of an abstraction to a variable preserves the invariant, by the
same two moves a binding of a variable makes. -/
theorem couple_appVar {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x z : Var}
    {r : Ref} (hc : Couple c hs ρ m) (hρ : ρ.lookup z = some r)
    (hm : 0 < (expand m).count r) :
    Couple c hs (TEnv.set ρ x r) (Multi.insert (Multi.dropFirst m r) x r) :=
  couple_bindVar hc hρ hm

/-- An application of an abstraction to an allocated value preserves the invariant,
by the same two moves a binding of an allocated value makes. -/
theorem couple_appVal {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x : Var}
    {v : Expr} {c' : CHeap} {hs' : List Ref} {r : Ref} (hv : ValRef c hs ρ v c' hs' r)
    (halloc : ∀ z, v ≠ .var z) (hc : Couple c hs ρ m) :
    Couple c' (dropHandle hs' r) (TEnv.set ρ x r) (Multi.insert m x r) :=
  couple_bindVal hv halloc hc

/-- A match on the cell a variable names preserves the invariant: it reads the cell's
slots into the arm's binders and changes no count, and the arm rebinds none of the
names the multiplicity holds. -/
theorem couple_match {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {z : Var}
    {ys : List Var} {r : Ref} (hc : Couple c hs ρ m)
    (_hρ : ρ.lookup z = some r) (_hlen : ys.length = (CHeap.slotsAt c r).length)
    (hfree : ∀ p ∈ m, p.1 ∉ ys) :
    Couple c hs (TEnv.bindAll ρ ys (CHeap.slotsAt c r)) m :=
  ⟨hc.wf, hc.counted, Bound.bindAll hc.bound hfree⟩

/-- The destructive branch of a store preserves the invariant: the multiplicity and
the run's handles are what they were, and the write's own counting theorem is what the
heap's counts follow. -/
theorem couple_store_exclusive {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi}
    {r : Ref} {v : Expr} {c₁ : CHeap} {hs₁ : List Ref} {wv : Ref} {i : Nat}
    (hc : Couple c hs ρ m) (hv : ValRef c hs ρ v c₁ hs₁ wv)
    (hchk : writeCheck c₁ r (storeSlots c₁ r i wv) = true) (h1 : CHeap.count c₁ r = 1) :
    Couple (update c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv)).1 hs₁ ρ m := by
  obtain ⟨hW₁, hcount₁, hbound⟩ := valRef_couple c hs ρ v c₁ hs₁ wv m hv hc
  have hExcl : Exclusive (CHeap.presentation c₁) (hs₁ ++ expand m) r :=
    (counted_iff_exclusive hcount₁ r).mp h1
  rw [update_of_count_one c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv) h1]
  refine ⟨?_, ?_, hbound⟩
  · simpa only [update_of_count_one c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv) h1]
      using CHeap.wf_update (handles := hs₁ ++ expand m) (r := r)
        (ks := storeSlots c₁ r i wv) hW₁
  · simpa only [update_of_count_one c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv) h1]
      using counted_update_exclusive (handles := hs₁ ++ expand m) (r := r)
        (ks := storeSlots c₁ r i wv) hW₁ hcount₁ hExcl (writeCheck_avoids hchk)
        (writeCheck_self hchk) (writeCheck_live hchk)

/-- The copying branch of a store preserves the invariant: the fresh cell joins the
run's handles while one occurrence of the old reference leaves the term's own, and the
subject variable names the fresh location. -/
theorem couple_store_shared {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var}
    {r : Ref} {v : Expr} {c₁ : CHeap} {hs₁ : List Ref} {wv : Ref} {i : Nat}
    (hc : Couple c hs ρ m) (hv : ValRef c hs ρ v c₁ hs₁ wv)
    (hchk : writeCheck c₁ r (storeSlots c₁ r i wv) = true) (hm : 0 < (expand m).count r)
    (h2 : CHeap.count c₁ r ≠ 1) :
    Couple (update c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv)).1 hs₁
      (TEnv.set ρ y (fresh c₁ (storeSlots c₁ r i wv)))
      (Multi.insert (Multi.dropFirst m r) y (fresh c₁ (storeSlots c₁ r i wv))) := by
  obtain ⟨hW₁, hcount₁, hbound⟩ := valRef_couple c hs ρ v c₁ hs₁ wv m hv hc
  have hks := writeCheck_avoids hchk
  have hself := writeCheck_self hchk
  have hlive := writeCheck_live hchk
  have hhandle : 1 ≤ (hs₁ ++ expand m).count r := by rw [List.count_append]; omega
  have hne : ¬ Exclusive (CHeap.presentation c₁) (hs₁ ++ expand m) r :=
    fun hx => h2 ((counted_iff_exclusive hcount₁ r).mpr hx)
  have hr : r ∈ CHeap.refs c₁ := by
    refine CHeap.mem_refs_of_count_pos c₁ ?_
    rw [(counted_iff_slots c₁ (hs₁ ++ expand m)).mp hcount₁ r]
    omega
  rw [update_of_count_ne_one c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv) h2]
  refine ⟨?_, ?_,
    Bound.insert
      (Bound.dropFirst (Bound.set hc.bound y (fresh c₁ (storeSlots c₁ r i wv))) r)
      (TEnv.lookup_set_self ρ y (fresh c₁ (storeSlots c₁ r i wv)))⟩
  · simpa only [update_of_count_ne_one c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv) h2]
      using CHeap.wf_update (handles := hs₁ ++ expand m) (r := r)
        (ks := storeSlots c₁ r i wv) hW₁
  · refine counted_of_count_eq ?_ (count_store_copy hs₁ m y (fresh_ne_of_mem_refs hr) hm)
    simpa only [update_of_count_ne_one c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv) h2]
      using counted_update_copy (handles := hs₁ ++ expand m) (r := r)
        (ks := storeSlots c₁ r i wv) hcount₁ hne hhandle hks hlive

/-! ## The per-step theorem -/

/-- Every target step preserves the coupling invariant, at the multiplicity the
instruction leaves and in the environment and on the handles it leaves. Each case is
its rule's own lemma above; the relation is not recursive, so a case analysis over the
step's rule is the whole of it. -/
theorem couple_step {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {e : Expr}
    {c' : CHeap} {hs' : List Ref} {ρ' : TEnv} {m' : Multi} {e' : Expr}
    (h : TStep c hs ρ m e c' hs' ρ' m' e') (hc : Couple c hs ρ m) : Couple c' hs' ρ' m' := by
  cases h with
  | dup hρ hlive => exact couple_dup hc hρ hlive
  | dropShared hρ h2 hm => exact couple_drop_shared hc hρ h2 hm
  | dropFinal hρ h1 hm => exact couple_drop_final hc hρ h1 hm
  | bindVar hρ hm => exact couple_bindVar hc hρ hm
  | bindVal hv halloc => exact couple_bindVal hv halloc hc
  | appVar hρ hm => exact couple_appVar hc hρ hm
  | appVal hv halloc => exact couple_appVal hv halloc hc
  | matchC hρ hlen hfree => exact couple_match hc hρ hlen hfree
  | storeExclusive hρ hv hi hchk h1 => exact couple_store_exclusive hc hv hchk h1
  | storeShared hρ hv hi hchk hm h2 => exact couple_store_shared hc hv hchk hm h2

/-! ## The multiplicity moves as the instructions do -/

/-- The term's multiplicity of a variable, read by tag: the occurrences the term
holds whose pair names that variable. -/
def Multi.weight (m : Multi) (x : Var) : Nat := (m.filter (fun p => p.1 = x)).length

/-- A `dup` step takes the term's multiplicity of the duplicated variable from `n` to
`n + 1`: the pair the instruction supplies is tagged with that variable and the rest
of the list is untouched. -/
theorem dup_multiplicity (m : Multi) (y : Var) (r : Ref) :
    Multi.weight (Multi.insert m y r) y = Multi.weight m y + 1 := by
  simp [Multi.weight, Multi.insert]

/-- A `drop` step takes the term's multiplicity of the dropped variable's reference
from `n + 1` to `n`: one occurrence of that reference leaves the term's own list. The
removal is read at the reference, because a pair's tag records the variable an
occurrence was read at while a `drop` is stated at the reference its variable names. -/
theorem drop_multiplicity {m : Multi} {r : Ref} (hm : 0 < (expand m).count r) :
    (expand (Multi.dropFirst m r)).count r + 1 = (expand m).count r := by
  rw [expand_dropFirst_count_self]
  omega

/-! ## The two store theorems -/

/-- An owned store is destructive. A store whose subject the term holds exactly once,
with no cell's slot and no handle the run holds naming that cell, is at a count of one;
`RCHeap.update` then takes its destructive branch, so the cell keeps its location and
the written slots are read back there.

The hypotheses, and where each comes from:

* `hc`, the coupling invariant: the configuration.
* `hρ`, the subject variable's reference: the store rule's environment premise.
* `hm`, the subject's multiplicity being one: the reading of the multiplicity, which
  the derivation's `dup` and `drop` instructions leave.
* `hslot`, no cell's slot naming the cell: not derivable here, and named — it is what
  the discipline's take-out provides, `Run.writeStep`'s take-out having emptied the
  slot the write lands at.
* `hrun`, no handle the run holds naming it: the same, and named — the take-out's pair
  is destructured and its handle dropped before the focus check
  (`Run.takeout_dropped_count_one`).
* `hks`, the written slots not naming the cell: the write rule's own check. -/
theorem store_owned_is_destructive {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi}
    {y : Var} {r : Ref} {ks : List Ref} (hc : Couple c hs ρ m) (_hρ : ρ.lookup y = some r)
    (hm : (expand m).count r = 1) (hslot : (CHeap.slots c).count r = 0) (hrun : hs.count r = 0)
    (hks : r ∉ ks) : (update c (hs ++ expand m) r ks).1.lookup r = some ks := by
  have hW := hc.wf
  have hcount := hc.counted
  have hcs := (counted_iff_slots c (hs ++ expand m)).mp hcount
  have h1 : CHeap.count c r = 1 := by
    rw [hcs r, hslot, List.count_append, hrun, hm]
  have hhandle : 1 ≤ (hs ++ expand m).count r := by
    rw [List.count_append, hrun, hm]
    omega
  exact update_preserves_location_of_exclusive hW hcount ((counted_iff_exclusive hcount r).mp h1)
    hhandle hks

/-- A shared store copies. A store whose subject the term holds twice, or whose cell a
heap slot also names, is at a count above one; `RCHeap.update` then takes its copying
branch, so the written slots land at a fresh location, the old cell keeps its slots and
loses a reference, and the fresh location is not one the heap listed.

The hypotheses, and where each comes from:

* `hc`, the coupling invariant: the configuration.
* `hρ`, the subject variable's reference: the store rule's environment premise.
* `hown`, the subject's multiplicity being positive: the reading of the multiplicity
  the derivation carries for the subject.
* `hm`, the multiplicity being two or more, or a heap slot naming the cell: the
  reading of the multiplicity or the heap.
* `hks`, the written slots not naming the cell: the write rule's own check. -/
theorem store_shared_copies {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var}
    {r : Ref} {ks : List Ref} (hc : Couple c hs ρ m) (_hρ : ρ.lookup y = some r)
    (hown : 0 < (expand m).count r)
    (hm : 2 ≤ (expand m).count r ∨ 1 ≤ (CHeap.slots c).count r) (hks : r ∉ ks) :
    (update c (hs ++ expand m) r ks).1.lookup (fresh c ks) = some ks ∧
      (update c (hs ++ expand m) r ks).1.lookup r = CHeap.lookup c r ∧
      (update c (hs ++ expand m) r ks).1.count r = CHeap.count c r - 1 := by
  have hcount := hc.counted
  have hcs := (counted_iff_slots c (hs ++ expand m)).mp hcount
  have hne1 : CHeap.count c r ≠ 1 := by
    intro h1
    rw [hcs r, List.count_append] at h1
    rcases hm with hm | hm <;> omega
  have hhandle : 1 ≤ (hs ++ expand m).count r := by rw [List.count_append]; omega
  have hne : ¬ Exclusive (CHeap.presentation c) (hs ++ expand m) r :=
    fun hx => hne1 ((counted_iff_exclusive hcount r).mpr hx)
  obtain ⟨hfresh_look, hlook, hcount', _⟩ := update_copies_of_shared hcount hne hhandle hks
  exact ⟨hfresh_look, hlook, hcount'⟩

end Scidonia.RC
