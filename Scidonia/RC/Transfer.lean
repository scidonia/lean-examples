/-
The transfer between the run model's configuration and the coupled account: what the
run's own handle list says about the coupling's split, and what the take-out's check
supplies of the write theorem's hypotheses.

`Scidonia.RC.Correspondence` is one route from a typed store to a destructive write: a
store's own write clause and a correspondence `Corr ρ m Γ` give
`Scidonia.RC.store_owned_is_destructive`'s two premises, and the correspondence's third
clause --- the account's tags being injective on references (`RefInj m`) --- is the
hypothesis nothing in that module derives. `Scidonia.FracPerm.StateVar.Run` is the other
route: its heap is `CHeap = List (Ref × Cell)`, its handle lists are `List Ref`, and its
take-out and nested write reach a count of one from the schema's own focus check
(`Run.exclusive_head`) without any injectivity, because it carries no names at all. The
two share the counted heap (`Scidonia.FracPerm.StateVar.RCHeap`'s `CHeap`, `Counted` and
`Exclusive`), so the *counts* are comparable even though the *tags* are not.

## The count transfer

At a nested write the schema has emptied the slot the write lands at and holds the
extracted occurrence as the caller's handle, so the run's handle list at the focus check
is `e :: hs` while the coupling's split is `hs ++ expand m`. The two read the same
references exactly when the account is the extracted occurrence
(`count_takeout_split`, `counted_couple_of_takeout`, and the same read back), and the
run's own handle list is the coupling's split exactly at the empty account
(`count_split_agree_iff`) --- at any other account the coupling's split names references
the run's list does not, which is the account's own contribution and not a second
handle. The transport is `Scidonia.RC.counted_of_count_eq` over the order lemma
`Scidonia.RC.count_cons_append_swap`, both already carried by the account's module, so
the counts are what transfers; the two list lemmas below are what reads an account's
identity back out of its counts, and nothing is added to the counted heap's own
theory.

## The composition at a nested write

`store_destructive_of_takeout` reads the run's side as the write theorem's two named
hypotheses: `Run.exclusive_head` gives the addressed cell no slot naming it and the
run's own handle the only name on it, which are `store_owned_is_destructive`'s `hslot`
and its `hrun`, and the count of one then follows from `counted_iff_exclusive`. The
composition's remaining inputs are named: the coupling at the run's handle list and the
extracted occurrence, the correspondence's name counts, the subject's lookup and the
write rule's own check on the written slots. `update_fst_eq_of_handles` is why the
write's result reads the same at the run's handle list as at the coupling's split: the
branch is the heap's own count and the handle list enters only the result's second
component, so the two orderings of one multiset give one write.

## The boundary

`RefInj` is not a function of the run-side facts alone. The run reads the account only
through `expand`, so two accounts with the same references are one configuration to it
and differ only in their tags: `refInj_not_determined` exhibits such a pair, one
injective and one not, together with the counting that is the same at every heap and
handle list. What makes the clause a fact of the transfer is the coupling beside the
run: the run's counting of `e :: hs` and the coupling's counting of `hs ++ expand m` of
one heap force the account to be that one extracted occurrence
(`expand_eq_singleton_of_counted`), and an account of one occurrence is injective
whatever it is named (`refInj_of_expand_singleton`, `refInj_of_counted`). So at the
configuration a nested write runs at, `Corr`'s third clause is a consequence of the two
countings and not an input: `store_destructive_of_corr` states the composition in the
correspondence's own vocabulary --- the caller supplies the correspondence's name counts,
the coupling its `Bound`, and the two countings its injectivity clause, so the structure
is built at the composition and no caller carries an injectivity proof.

## What is modelled, and what is trusted

The transfer is a statement about this model's heaps, handle lists and accounts, and
about nothing else: the handle lists are lists of names, the account's references are
the occurrences a `Multi` lists, and the counts are the counted heap's own. The
identification it rests on is the schema's own --- the handle list `e :: hs` at the
nested focus check is the outer handles with the extracted occurrence at the head, and
the coupling's split is the same outer handles with the account's references after
them --- and it needs nothing about the heap beyond the two countings. The run model
carries its own destructive-write guarantees without this account, and they stand beside
these statements unchanged: `Run.writeStep_lands` is the per-step statement at an
accepted configuration and `Run.every_write_step_keeps_its_address` is the per-run one,
each about `Run.writeStep`'s own steps.

What is here is the two routes read at one configuration of a write step.
`couple_of_takeout` states the coupling at the configuration the step's take-out hands the
nested write: the run's counting at the level beside the account that names the occurrence
the take-out extracted --- the account's identity `expand m = [e]` is that statement's own
hypothesis, since it is the coupling being built and the counting the identity would
otherwise be read from does not exist yet --- and `couple_at_run_handles_is_empty` is why the
account is read out of the run's own handle list rather than added beside it --- the
coupling's split and the run's list hold the same handles only at the empty account.
`store_destructive_of_takeout` and `store_destructive_of_corr` are handed the coupling, whose
own counting is the second counting, so there `expand_eq_singleton_of_counted` reads the
account's identity off it beside the run's counting and the identity is no input of theirs.
`writeStep_focus` and `writeStep_recurses` read the schema's check and its recursion off the
step itself, and
`writeStep_nested_destructive_of_couple` composes them: the take-out of a write step of an
accepted configuration, the account the term holds there through the coupling, and the
schema's checks are the write theorem's two premises, so the destructive branch at the
nested subject is a statement about that step, with `Run.writeStep_spec`'s own result beside
it and the correspondence's injectivity clause built from the two countings rather than
carried (`store_destructive_of_corr`). `writeStep_subject_destructive_of_couple` is the same
composition at a write whose path's level is its last, where the recursion's entry is the
write's own subject and the leaf's check supplies the write rule's premise on the written
slots. What is still not here is the program: the composition reads one step's recursion at
one configuration, from an accepted configuration, and the induction over a whole program's
steps is `Run.every_write_step_keeps_its_address`'s own. Nothing here is about compiled code,
and nothing in it runs.
-/
import Scidonia.RC.Correspondence
import Scidonia.FracPerm.StateVar.Run

namespace Scidonia.RC

open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap
open Scidonia.FracPerm.StateVar.Run

/-! ## The account's reference list, read as a list of names

The transport between the two readings of an occurrence list is the account's own
`counted_of_count_eq`, and the order it needs is the account's own
`count_cons_append_swap`: the run's take-out puts the extracted occurrence at the head
of the handle list, and the account puts it at the end of the references the coupling's
split carries after the handles. The two lemmas below read a list of references out of
its counts, which is what makes the account's identity a consequence of the two
countings rather than an extra hypothesis. -/

/-- A reference list every element of which is `e` is counted at `e` as often as it is
long: the counting of an occurrence list whose elements are all one reference. -/
theorem count_self_eq_length_of_all_eq {l : List Ref} {e : Ref} (h : ∀ x ∈ l, x = e) :
    l.count e = l.length := by
  induction l with
  | nil => rfl
  | cons y t ih =>
      have hy : y = e := h y (by simp)
      rw [hy, List.count_cons_self, List.length_cons,
        ih (fun x hx => h x (List.mem_cons_of_mem y hx))]

/-- The counts at every reference determine a one-occurrence list: a list counted once
at `e` and nowhere else is the list `[e]`. -/
theorem eq_singleton_of_count {l : List Ref} {e : Ref}
    (h : ∀ x, l.count x = if x = e then 1 else 0) : l = [e] := by
  have hall : ∀ x ∈ l, x = e := by
    intro x hx
    by_cases hne : x = e
    · exact hne
    · exfalso
      have hz := h x
      rw [ite_eq_right hne] at hz
      have hpos : 0 < l.count x := List.count_pos_iff.mpr hx
      omega
  have hlen : l.length = 1 := by
    have hcount : l.count e = 1 := by rw [h e, ite_eq_left rfl]
    rw [count_self_eq_length_of_all_eq hall] at hcount
    exact hcount
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  rw [ha] at hall ⊢
  rw [hall a (by simp)]

/-! ## The count transfer

The run's handle list at the nested focus check and the coupling's split name the same
references when the account is the extracted occurrence, and the run's own list is the
coupling's split exactly at the empty account. -/

/-- The run's handle list at the take-out and the coupling's split read the same counts:
the extracted occurrence is the run's head, and the account is the same occurrence
written after the handles. -/
theorem count_takeout_split (hs : List Ref) (m : Multi) (e : Ref) (hm : expand m = [e])
    (x : Ref) : (hs ++ expand m).count x = (e :: hs).count x := by
  rw [hm]
  have h := count_cons_append_swap e hs ([] : List Ref) x
  rwa [List.append_nil] at h

/-- The count transfer: the run's counting of its own handles is the coupling's counting
of its split, when the account is the occurrence the take-out moved out of the slots. -/
theorem counted_couple_of_takeout {c : CHeap} {hs : List Ref} {m : Multi} {e : Ref}
    (h : Counted c (e :: hs)) (hm : expand m = [e]) : Counted c (hs ++ expand m) :=
  counted_of_count_eq h fun x => count_takeout_split hs m e hm x

/-- The count transfer reads back: the coupling's counting of its split is the run's
counting of its own handles. -/
theorem counted_takeout_of_couple {c : CHeap} {hs : List Ref} {m : Multi} {e : Ref}
    (h : Counted c (hs ++ expand m)) (hm : expand m = [e]) : Counted c (e :: hs) :=
  counted_of_count_eq h fun x => (count_takeout_split hs m e hm x).symm

/-- The run's own handle list is the coupling's split exactly at the empty account:
adding the account's references to the run's handles leaves every count where it was
only when the account names no reference at all. -/
theorem count_split_agree_iff (hs : List Ref) (m : Multi) :
    (∀ x, (hs ++ expand m).count x = hs.count x) ↔ m = [] := by
  constructor
  · intro h
    by_cases hne : m = []
    · exact hne
    · exfalso
      have hex : expand m ≠ [] := fun hz => hne (List.map_eq_nil_iff.mp hz)
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (expand m) hex
      have hpos : 0 < (expand m).count x := List.count_pos_iff.mpr hx
      have hz := h x
      rw [List.count_append] at hz
      omega
  · intro h
    subst h
    simp

/-! ## The write at the take-out's configuration

The update's branch is the heap's own count and its result's second component is the
handle list it was handed, so the heap a write leaves reads the same at the run's list
and at the coupling's split, and the take-out's check is what takes the destructive
branch. -/

/-- The heap a write leaves does not depend on the handle list it was handed: the branch
is the heap's own count, and the handle list enters only the result's second
component. -/
theorem update_fst_eq_of_handles (c : CHeap) (h₁ h₂ : List Ref) (r : Ref) (ks : List Ref) :
    (update c h₁ r ks).1 = (update c h₂ r ks).1 := by
  by_cases h : CHeap.count c r = 1
  · rw [update_of_count_one c h₁ r ks h, update_of_count_one c h₂ r ks h]
  · rw [update_of_count_ne_one c h₁ r ks h, update_of_count_ne_one c h₂ r ks h]

/-- The take-out's check decides the update's branch: the run's counting reads the focus
check as a count of one, so the write at the extracted occurrence is the counted heap's
destructive update and the extracted occurrence stays the handle the write holds. -/
theorem takeout_update_destructive {c : CHeap} {hs : List Ref} {e : Ref} {ks : List Ref}
    (hcounted : Counted c (e :: hs)) (hex : Exclusive (CHeap.presentation c) (e :: hs) e) :
    update c (e :: hs) e ks = (CHeap.cascade (CHeap.writeSlots c e ks), e :: hs) :=
  update_of_count_one c (e :: hs) e ks ((counted_iff_exclusive hcounted e).mpr hex)

/-! ## The composition at a nested write

The take-out's check and the run's counting are the write theorem's `hslot` and its
`hrun`, the two countings together are the account's identity, and the correspondence's
name counts are all the composition reads of the typing. -/

/-- The run's counting and the coupling's counting of one heap determine the account:
the account's references are the one occurrence the take-out extracted. -/
theorem expand_eq_singleton_of_counted {c : CHeap} {hs : List Ref} {m : Multi} {e : Ref}
    (hrun : Counted c (e :: hs)) (hcouple : Counted c (hs ++ expand m)) :
    expand m = [e] := by
  refine eq_singleton_of_count fun x => ?_
  have h1 := (counted_iff_slots c (e :: hs)).mp hrun x
  have h2 := (counted_iff_slots c (hs ++ expand m)).mp hcouple x
  rw [List.count_append] at h2
  by_cases he : x = e
  · subst he
    rw [List.count_cons_self] at h1
    rw [ite_eq_left rfl]
    omega
  · rw [List.count_cons_of_ne (b := e) (a := x) (fun hh => he hh.symm)] at h1
    rw [ite_eq_right he]
    omega

/-- An account whose references are one occurrence is injective: it holds one pair, and
the tags of one pair cannot disagree. -/
theorem refInj_of_expand_singleton {m : Multi} {e : Ref} (h : expand m = [e]) : RefInj m := by
  have hlen : m.length = 1 := by
    have hmap := congrArg List.length h
    simpa [expand] using hmap
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hlen
  rw [hp]
  intro q hq q' hq' _
  simp only [List.mem_singleton] at hq hq'
  rw [hq, hq']

/-- The take-out supplies the correspondence's injectivity: the run's counting and the
coupling's counting of one heap leave the account the one extracted occurrence, whose
tags are injective whatever names they carry. -/
theorem refInj_of_counted {c : CHeap} {hs : List Ref} {m : Multi} {e : Ref}
    (hrun : Counted c (e :: hs)) (hcouple : Counted c (hs ++ expand m)) : RefInj m :=
  refInj_of_expand_singleton (expand_eq_singleton_of_counted hrun hcouple)

/-- **The nested write's destructive branch.** The run's counting of its handles beside
the take-out's focus check gives the written cell no slot naming it and the run's own
handle the only name on it --- `store_owned_is_destructive`'s `hslot` and its `hrun` ---
and the coupling's counting of the same heap leaves the account the extracted
occurrence, so the account's count of one follows without the correspondence's
injectivity: the write takes the destructive branch and the addressed cell keeps its
location.

The coupling's run handles are the run's own tail and its account the occurrence the
take-out extracted; the write rule's own check on the written slots (`hks`) is the
rule's premise and not the transfer's. -/
theorem store_destructive_of_takeout {c : CHeap} {hs : List Ref} {m : Multi} {e : Ref}
    {ks : List Ref} {ρ : TEnv} {Γ Δ : Occs} {y : Var} {i : Nat} {v : Expr}
    (hcouple : Couple c hs ρ m) (hcounted : Counted c (e :: hs))
    (hex : Exclusive (CHeap.presentation c) (e :: hs) e)
    (hname : ∀ x, countName m x = Γ.count x) (hlook : ρ.lookup y = some e)
    (hstore : Typed Δ Γ (.store (.var y) i v)) (hks : e ∉ ks) :
    (update c (e :: hs) e ks).1.lookup e = some ks := by
  obtain ⟨hslots, _hhold, htail⟩ := exclusive_head hex rfl
  have hsingle : expand m = [e] := expand_eq_singleton_of_counted hcounted hcouple.counted
  have howns : Owns ρ m (.store (.var y) i v) :=
    owns_of_correspondence (Γ := Γ) hcouple.bound (hname y) (Typed.store_count hstore) hlook
  have hm : (expand m).count e = 1 := by rw [hsingle]; simp
  have hmain := store_owned_is_destructive hcouple hlook howns hm hslots htail hks
  rw [hsingle, update_fst_eq_of_handles c (hs ++ [e]) (e :: hs) e ks] at hmain
  exact hmain

/-- **The composition in the correspondence's own vocabulary.** The caller supplies the
correspondence's name counts beside the coupling, and the composition builds `Corr ρ m Γ`
itself: `Bound` is the coupling's own, and the injectivity clause is the consequence
`refInj_of_counted` reads off the run's counting and the coupling's counting of the same
heap. That built structure is what the write theorem's two premises are read off
(`bridge`, through `store_owned_is_destructive`) --- the subject's occurrence in the
account and the account's count of the reference the environment names for it --- so the
conclusion is `store_destructive_of_takeout`'s, reached through the correspondence rather
than off the take-out's check alone. No injectivity proof is an input: at the
configuration a nested write runs at, `Corr`'s third clause is the two countings'
consequence and not a hypothesis to carry. -/
theorem store_destructive_of_corr {c : CHeap} {hs : List Ref} {m : Multi} {e : Ref}
    {ks : List Ref} {ρ : TEnv} {Γ Δ : Occs} {y : Var} {i : Nat} {v : Expr}
    (hcouple : Couple c hs ρ m) (hcounted : Counted c (e :: hs))
    (hex : Exclusive (CHeap.presentation c) (e :: hs) e)
    (hname : ∀ x, countName m x = Γ.count x)
    (hlook : ρ.lookup y = some e) (hstore : Typed Δ Γ (.store (.var y) i v)) (hks : e ∉ ks) :
    (update c (e :: hs) e ks).1.lookup e = some ks := by
  have hcorr : Corr ρ m Γ :=
    ⟨hcouple.bound, hname, refInj_of_counted hcounted hcouple.counted⟩
  obtain ⟨hslots, _hhold, htail⟩ := exclusive_head hex rfl
  obtain ⟨howns, hcount⟩ := bridge (i := i) (v := v) hcorr hlook (Typed.store_count hstore)
  have hmain := store_owned_is_destructive hcouple hlook howns hcount hslots htail hks
  rw [update_fst_eq_of_handles c (hs ++ expand m) (e :: hs) e ks] at hmain
  exact hmain

/-! ## The boundary

The run reads the account through `expand` alone, so the tags are free of it; what pins
the account is the coupling's counting beside the run's, which fixes the account's size
and with it its injectivity. -/

/-- Two accounts whose references are the same list are one configuration to the run's
side: every counting fact about the coupling's split is a fact of `expand` alone. -/
theorem counted_split_congr {c : CHeap} {hs : List Ref} {m₁ m₂ : Multi}
    (h : expand m₁ = expand m₂) :
    (Counted c (hs ++ expand m₁) ↔ Counted c (hs ++ expand m₂)) := by
  rw [h]

/-- Two accounts the run's side cannot separate: `[(0, 0), (0, 0)]` and `[(0, 0),
(1, 0)]` are both read as the references `[0, 0]`, so every counting fact about the
coupling's split holds of both --- and the first is injective where the second names the
reference `0` twice. -/
theorem refInj_not_determined :
    ∃ m₁ m₂ : Multi, expand m₁ = expand m₂ ∧ RefInj m₁ ∧ ¬ RefInj m₂ ∧
      (∀ (c : CHeap) (hs : List Ref), Counted c (hs ++ expand m₁) ↔ Counted c (hs ++ expand m₂)) := by
  refine ⟨[(0, 0), (0, 0)], [(0, 0), (1, 0)], rfl, ?_, ?_, fun c hs => counted_split_congr rfl⟩
  · intro p hp q hq _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rfl
  · simpa [aliasM] using alias_not_inj

/-! ## The configuration the take-out hands the nested write

`Run.writeStep`'s recursion is a sequence of take-outs. At a level the schema takes the
element the path's index names out of the cell at hand, hands back the pair, drops the
pair's handle, checks the element it extracted, and recurses into that element, so the
configuration it hands the nested write is the take-out's: the heap loses the extracted
occurrence from the cell at hand's slots, the run's handle list gains it at the head, and
the recursion enters the extracted element with that handle list.

The coupling at that configuration is therefore a statement about the take-out. The
coupling's split is the run's handle list with the account's references *read out of it*:
at the level the run holds `hs` whose head names the cell at hand, and at the level below
it holds `e :: hs` while the coupling's handles are `hs` and its account names `e` --- the
occurrence the take-out moved into the run's handle. The account is not a second handle
beside the run's, and `couple_at_run_handles_is_empty` is why it cannot be: the coupling's
split and the run's own handle list hold the same handles only at the empty account, so at
the run's own list the account's occurrence is the head of that list and the coupling's
handles are what follows it.

The account's identity `expand m = [e]` is the two countings' identity at the level below,
and the statements that receive an already-built coupling derive it there:
`store_destructive_of_takeout` and `store_destructive_of_corr` hold the coupling, whose own
counting is the second counting, so `expand_eq_singleton_of_counted` reads the identity off
it beside the run's counting and the identity is no input of theirs. `couple_of_takeout`
takes it as its caller's hypothesis and must: it is the statement that *builds* the coupling,
so at the point it applies the second counting does not exist yet, and there is nothing for
`expand_eq_singleton_of_counted` to read the identity from. `couple_of_takeout` is the
coupling at one level. `writeStep_focus` and `writeStep_recurses` are the two facts about
`Run.writeStep` the statement is applied at: the check the schema makes is the one the
take-out's result carries, the pair's drop cancelling the increment, and the step's result is
the put-back of the recursion's.

## The run's own write, read through the coupling

`writeStep_nested_destructive_of_couple` is the composition at a write step of an accepted
configuration: the step's own take-out hands the nested write the configuration
`couple_of_takeout`'s coupling is stated at, the schema's checks are the write theorem's
two premises, and the write at the cell the recursion entered is the counted heap's
destructive branch, reached through the correspondence --- its injectivity clause built from
the two countings (`store_destructive_of_corr`) rather than carried. The step's own result
stands beside it, which is `Run.writeStep_spec`'s, so the run's route and the typing's route
are read at one configuration. `writeStep_subject_destructive_of_couple` is the same
composition at a write whose path's level is its last: there the recursion's entry *is* the
write's subject, so the leaf's check supplies the write rule's premise and the two routes'
conclusions are about one cell. -/

/-- The coupling's split and the run's own handle list hold the same handles only at the
empty account: a coupling stated at the run's own list names no occurrence. So the account
at a nested write is read out of the run's handle list --- the extracted occurrence is that
list's head, and the coupling's handles are what follows it --- and not added to it. -/
theorem couple_at_run_handles_is_empty {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi}
    (hcounted : Counted c hs) (hc : Couple c hs ρ m) : m = [] := by
  refine (count_split_agree_iff hs m).mp fun x => ?_
  have h1 := (counted_iff_slots c hs).mp hcounted x
  have h2 := (counted_iff_slots c (hs ++ expand m)).mp hc.counted x
  omega

/-- **The coupling at the configuration the take-out hands the nested write.** The take-out's
own statement counts the configuration it leaves at the run's handle list --- the heap's counts
are what they were and the list is the level's with the extracted occurrence at its head ---
and the account the recursion hands names that occurrence, so the coupling at that
configuration is the run's counting read through the account: its handles are the level's
handle list and its account the extracted occurrence, which is the level's account's pair read
again as the run's new head.

The run's handle list's head names the cell at hand, so the level's focus check is what puts
the addressed cell's only name on that handle. The account's clause is `Bound` and the run
supplies the counting; the account is not a second handle beside the run's list. -/
theorem couple_of_takeout {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {r : Ref}
    {i : Nat} {e : Ref} (hW : CHeap.WF c) (hcounted : Counted c hs)
    (hhead : hs.head? = some r) (hex : Exclusive (CHeap.presentation c) hs r)
    (hlook : (CHeap.slotsAt c r)[i]? = some e)
    (hbound : Bound ρ m) (hsize : expand m = [e]) :
    Couple (held c r i e) hs ρ m := by
  have hcount : CHeap.count c r = 1 := (counted_iff_exclusive hcounted r).mpr hex
  have hr : r ∈ CHeap.refs c := CHeap.mem_refs_of_count_pos c (by omega)
  obtain ⟨hclean, _hhold, _htail⟩ := exclusive_head hex hhead
  have hself : r ∉ CHeap.slotsAt c r := by
    intro hmem
    have hpos : 0 < (CHeap.slotsAt c r).count r := List.count_pos_iff.mpr hmem
    have hle := CHeap.slotsAt_count_le_slots c r hr r
    omega
  have hks : r ∉ eraseAt (CHeap.slotsAt c r) i := fun hmem => hself (mem_eraseAt hmem)
  have hlive : ∀ x ∈ eraseAt (CHeap.slotsAt c r) i, x ∈ CHeap.refs c := fun x hx =>
    mem_refs_of_mem_slots hcounted (mem_slots_of_mem_slotsAt hr (mem_eraseAt hx))
  have htake : Counted (held c r i e) (e :: hs) :=
    takeOut_counted hcounted hr hlook hks hself hlive
  refine ⟨?_, counted_couple_of_takeout htake hsize, hbound⟩
  show CHeap.WF (takeOut c hs r i e).1
  rw [CHeap.WF, takeOut_refs]
  exact hW

/-- **The schema's focus check.** A write step at a path with a level checks the element it
took out, at the heap and the handle list the take-out left: the pair's drop cancels the
increment, so the check the schema makes there is the one the take-out's result carries. -/
theorem writeStep_focus {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {p : Path}
    {ks : List Ref} {e : Ref} {c' : CHeap} {hs' : List Ref}
    (hlook : (CHeap.slotsAt c r)[i]? = some e)
    (h : writeStep c hs r (i :: p) ks = some (c', hs')) :
    exclusive? (held c r i e) (e :: hs) e = true := by
  rw [writeStep_cons] at h
  simp only [hlook] at h
  by_cases hchk : exclusive? c hs r = true
  · rw [ite_eq_left hchk] at h
    simp only [pair_dup_decRef_fst, pair_dup_decRef_snd, takeOut_fst_held, takeOut_handles] at h
    by_cases hfoc : exclusive? (held c r i e) (e :: hs) e = true
    · exact hfoc
    · rw [ite_eq_right hfoc] at h
      exact absurd h (by simp)
  · rw [ite_eq_right hchk] at h
    exact absurd h (by simp)

/-- **The schema's recursion.** A write step at a path with a level recurses into the
element it took out, at the configuration the take-out left, and puts the recursion's
result back where it came from: the step's result is that put-back. -/
theorem writeStep_recurses {c : CHeap} {hs : List Ref} {r : Ref} {i : Nat} {p : Path}
    {ks : List Ref} {e : Ref} {c' : CHeap} {hs' : List Ref}
    (hlook : (CHeap.slotsAt c r)[i]? = some e)
    (h : writeStep c hs r (i :: p) ks = some (c', hs')) :
    ∃ c₁ hs₁, writeStep (held c r i e) (e :: hs) e p ks = some (c₁, hs₁) ∧
      plug c₁ hs₁ r i (hs₁.headD e) = some (c', hs') := by
  rw [writeStep_cons] at h
  simp only [hlook] at h
  by_cases hchk : exclusive? c hs r = true
  · rw [ite_eq_left hchk] at h
    simp only [pair_dup_decRef_fst, pair_dup_decRef_snd, takeOut_fst_held, takeOut_handles] at h
    by_cases hfoc : exclusive? (held c r i e) (e :: hs) e = true
    · rw [ite_eq_left hfoc] at h
      cases hdeep : writeStep (held c r i e) (e :: hs) e p ks with
      | none =>
          rw [hdeep] at h
          exact absurd h (by simp)
      | some rest =>
          rw [hdeep] at h
          exact ⟨rest.1, rest.2, rfl, h⟩
    · rw [ite_eq_right hfoc] at h
      exact absurd h (by simp)
  · rw [ite_eq_right hchk] at h
    exact absurd h (by simp)

/-- **The composition at a write step's recursion.** A write step of an accepted
configuration --- the run's own write, at a path with a level --- hands the nested write the
configuration its take-out left, and the account the term holds there names the occurrence
it extracted. The take-out's own statement counts that configuration at the run's handle
list, the account's clause turns that counting into the coupling at it, and the schema's
checks are the write theorem's two premises, so the nested subject's write is the counted
heap's destructive branch, read through the correspondence the coupling and the two
countings build (`store_destructive_of_corr`) rather than off the take-out's check alone.

The composition is stated at the take-out's immediate cell: the coupling and the write read
off it are about `e`, the element the step's first level extracted and the recursion entered,
whatever the path below that level does with it.

The step's own result stands beside them, which is `Run.writeStep_spec`'s: the handle list is
what it was, and the path resolves to a cell `t` --- the leaf the step ultimately writes ---
whose written slots are read back there. At a path whose level is its last `t` is `e`, the
cell the coupling is read at; at a path of length at least two `t` is a cell below `e`, so
there the step's own result is about the leaf and the coupling is about the immediate cell.
The write rule's own check on the written slots (`hks`) is the rule's premise and not the
transfer's. -/
theorem writeStep_nested_destructive_of_couple {root : Ref} {c : CHeap} {hs : List Ref}
    {vs : List Scidonia.FracPerm.StateVar.Value} {ρ : TEnv} {m : Multi} {i : Nat}
    {p : Path} {ks : List Ref}
    {e : Ref} {c' : CHeap} {hs' : List Ref} {Γ Δ : Occs} {y : Var} {j : Nat} {v : Expr}
    (hacc : Accept root c hs vs)
    (hstep : writeStep c hs root (i :: p) ks = some (c', hs'))
    (hlook : (CHeap.slotsAt c root)[i]? = some e)
    (hbound : Bound ρ m) (hsize : expand m = [e]) (hks : e ∉ ks)
    (hname : ∀ x, countName m x = Γ.count x) (hlookup : ρ.lookup y = some e)
    (hstore : Typed Δ Γ (.store (.var y) j v)) :
    Couple (held c root i e) hs ρ m ∧
      (update (held c root i e) (e :: hs) e ks).1.lookup e = some ks ∧
      hs' = hs ∧ ∃ t, resolve c root (i :: p) = some t ∧ c'.lookup t = some ks := by
  have hhead : hs.head? = some root := by rw [hacc.handles]; rfl
  have hex : Exclusive (CHeap.presentation c) hs root :=
    exclusive?_eq_true (writeStep_check hstep)
  have hcouple : Couple (held c root i e) hs ρ m :=
    couple_of_takeout hacc.healthy.1 hacc.counted hhead hex hlook hbound hsize
  have hentry : Counted (held c root i e) (e :: hs) :=
    counted_takeout_of_couple hcouple.counted hsize
  have hfocus : Exclusive (CHeap.presentation (held c root i e)) (e :: hs) e :=
    exclusive?_eq_true (writeStep_focus hlook hstep)
  obtain ⟨t, ht⟩ := writeStep_resolve_of_eq hstep
  obtain ⟨hlookT, hlistT, _⟩ := writeStep_spec hacc.healthy hacc.counted hhead ht hstep
  exact ⟨hcouple,
    store_destructive_of_corr hcouple hentry hfocus hname hlookup hstore hks,
    hlistT, t, ht, hlookT⟩

/-- **The two routes at one cell.** The same composition at a write step whose path's level
is its last: the recursion's entry is the write's own subject, so the leaf's check supplies
the write rule's premise on the written slots and both routes' conclusions are about that
cell --- the run's step reads the written slots back at it (`Run.writeStep_spec`'s result)
and the coupling's update is the counted heap's destructive branch there. -/
theorem writeStep_subject_destructive_of_couple {root : Ref} {c : CHeap} {hs : List Ref}
    {vs : List Scidonia.FracPerm.StateVar.Value} {ρ : TEnv} {m : Multi} {i : Nat}
    {ks : List Ref} {e : Ref}
    {c' : CHeap} {hs' : List Ref} {Γ Δ : Occs} {y : Var} {j : Nat} {v : Expr}
    (hacc : Accept root c hs vs)
    (hstep : writeStep c hs root [i] ks = some (c', hs'))
    (hlook : (CHeap.slotsAt c root)[i]? = some e)
    (hbound : Bound ρ m) (hsize : expand m = [e])
    (hname : ∀ x, countName m x = Γ.count x) (hlookup : ρ.lookup y = some e)
    (hstore : Typed Δ Γ (.store (.var y) j v)) :
    Couple (held c root i e) hs ρ m ∧
      (update (held c root i e) (e :: hs) e ks).1.lookup e = some ks ∧
      c'.lookup e = some ks := by
  have hks : e ∉ ks := by
    obtain ⟨c₁, hs₁, hrec, _⟩ := writeStep_recurses (p := []) hlook hstep
    rw [writeStep_nil] at hrec
    by_cases hchk : (exclusive? (held c root i e) (e :: hs) e &&
        namesLive (held c root i e) ks && avoids ks e) = true
    · exact avoids_eq_true (Bool.and_eq_true_iff.mp hchk).2
    · rw [ite_eq_right hchk] at hrec
      exact absurd hrec (by simp)
  obtain ⟨hcpl, hdest, _, t, ht, hl⟩ :=
    writeStep_nested_destructive_of_couple (p := []) hacc hstep hlook hbound hsize hks
      hname hlookup hstore
  have ht1 : t = e := by
    rw [resolve_cons c root i [] e hlook, resolve_nil] at ht
    exact (Option.some.inj ht).symm
  exact ⟨hcpl, hdest, by rw [ht1] at hl; exact hl⟩

end Scidonia.RC
