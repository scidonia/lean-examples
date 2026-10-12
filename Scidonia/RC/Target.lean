/-
The target semantics: the A-normal runtime of λ¹'s heap semantics, at the counted
heap of `Scidonia.FracPerm.StateVar.RCHeap`.

Reinking, Xie, de Moura and Leijen, *Perceus: Garbage Free Reference Counting with
Reuse* (PLDI 2021) gives λRC a heap semantics (Figure 7) in which a node's slot is
replaced destructively exactly when the node's count is one, and in which a node
another reference also names is copied. This module is that runtime for the terms
of `Scidonia.RC.Syntax`, instantiated at this repository's counted heap: the
operations it performs are `RCHeap`'s own — `alloc` for a fresh node or closure,
`CHeap.adjust` for the runtime's increment and non-final decrement, `release` for
the final release, and `update` for the write in its two branches, whose branch is
the heap's own count. The `CHeap` the semantics runs on is the one
`Scidonia/FracPerm/StateVar/RCHeap.lean` defines and characterises, and nothing
here redefines it.

**Configurations, and the evaluation contexts.** A configuration is a heap, the
handles held outside the term, a runtime environment binding variables to
references, the term's own multiplicities and the term. The rules are one per
instruction, and a step also reaches the positions λ¹'s own heap semantics reaches:
the function position of an application, its argument position while the function
is a value, the right-hand side of a binding, and the fields of a node
construction. A-normal form is a statement about the *source* — its subjects and
its arguments are values, and the lowering sequences the computations that produce
them into bindings — and not about this term having no contexts: the lowering
places the duplication and the release instructions the source does not have in
exactly those positions, so an application's two positions, a binding's
right-hand side and a construction's fields can each hold a computation here, and
the congruence rules below reach every one of them. The argument position is the
source's own: the function is required to be a value, which is `Scidonia.RC.Pure`'s
`Value` at this shared syntax. The subjects a rule reads through the environment
are variables; a node construction in a value position is realised by `ValRef`,
which allocates its cell; and a write's subject is the variable the derivation
bound, which is what makes the store's branch a statement about that variable's
reference.

The multiplicities are part of the configuration rather than read off the term,
because an instruction moves them against the term's own occurrences: a `dup x; e`
step takes the term's multiplicity of `x` from `n` to `n + 1` — the instruction
supplies the occurrence `e` uses and the term `dup x; e` writes — and a `drop x; e`
step takes it from `n + 1` to `n`. An instruction that consumes an occurrence reads
it out of the term's own account rather than out of a count: a `drop`, a binding of
a variable, an application to a variable and a store each require the pair of the
variable they read and the reference the environment names for it to be one the
term holds (`Owns`), and the instruction's move takes exactly that pair out. The
counts the heap keeps are `Counted`'s, stated at the run's handles together with
the term's own references; `Scidonia.RC.Ownership` is that statement and its
preservation.

**The environment is the runtime's, not a substitution.** A binder extends the
environment and the term continues; nothing is substituted, so a variable in
function position is a variable and not a function — the same limit
`Scidonia.RC.Pure` states for the source's own reduction. The lowering's
environment is a different object: it is the *ownership* account a derivation
carries, and `Ownership` states what this module's counts have to do with it.

**What the write models, and what it does not.** A store's step is `RCHeap.update`
at the subject's reference with the slot list `i` set to the value's reference, so
its branch is the heap's own count: the branch of `isExclusiveUnsafe` /
`lean_array_uset` that decides whether a write mutates or copies. That decision
lives inside the runtime's emitted array-write code and is not a branch of the
emitted IR, so it is modelled here and trusted there, exactly as
`Scidonia/FracPerm/StateVar/RCHeap.lean` and `Run.lean` state it. A location is a
`Ref`: a name in a list, not a machine address; the fresh location a copy takes is
a model location beyond every reference the heap and the new slots mention, and
in-place updating is a fact of *this* model and not of any compiled code. That
Lean's compiler lowers this repository's own write paths — the sealed surface's
`set` and a leaf write such as the slot's `setLeaf` — into the shape modelled here
is checked by `ScidoniaTest/IRShape.lean`, which reads the post-reference-counting
IR, and is otherwise trusted.

**What is modelled, and what is trusted, beside the write's branch.** The
environment is dynamic and the model's closures capture nothing: a `lam` realises a
cell holding no slots, and an application's body reads its free variables from the
environment in force at the step. A match reads no tag, because a cell of the
counted heap carries slots and a count and no tag; the match's subject is therefore
a variable whose cell the arm's binders read. A value's reference is realised on
demand, so a node construction has a step exactly where a rule consumes it as a
value and a node construction standing alone as a whole program has none — the term
language has no location form for a construction's result. Same for an abstraction
in value position: the closure is allocated where it is bound or passed.
-/
import Scidonia.FracPerm.StateVar.RCHeap
import Scidonia.RC.Syntax
import Scidonia.RC.Pure

namespace Scidonia.RC

open Scidonia.FracPerm.StateVar.Footprint
open Scidonia.FracPerm.StateVar.RCHeap

/-! ## Environments and multiplicities

An environment is the reference a variable names, and a term's multiplicities are
the occurrences it holds: one pair per occurrence, the variable it was read at and
the reference it names. `expand` projects the references, and it is those — not the
tags — that `Counted` reads. -/

/-- A runtime environment: the reference each variable is bound to, as a list whose
first pair for a name is the one the name names, so a later binding shadows an
earlier one. -/
abbrev TEnv := List (Var × Ref)

/-- The reference a variable names, or `none` when the environment binds it
nowhere. -/
def TEnv.lookup : TEnv → Var → Option Ref
  | [], _ => none
  | (y, r) :: t, x => if y = x then some r else TEnv.lookup t x

/-- An empty environment binds nothing. -/
@[simp] theorem TEnv.lookup_nil (x : Var) : TEnv.lookup [] x = none := rfl

/-- The environment's first pair for a name is what the name names. -/
@[simp] theorem TEnv.lookup_cons_self (x : Var) (r : Ref) (t : TEnv) :
    TEnv.lookup ((x, r) :: t) x = some r := by
  simp [TEnv.lookup]

/-- A pair for another name leaves the lookup to the rest of the environment. -/
theorem TEnv.lookup_cons_of_ne {y x : Var} (h : y ≠ x) (r : Ref) (t : TEnv) :
    TEnv.lookup ((y, r) :: t) x = TEnv.lookup t x := by
  simp only [TEnv.lookup, ite_eq_right h]

/-- The environment a binding extends: the new pair is the first the lookup reads,
so the binding shadows every earlier one of the same name. -/
def TEnv.set (ρ : TEnv) (x : Var) (r : Ref) : TEnv := (x, r) :: ρ

/-- A binding's own name reads back its reference. -/
@[simp] theorem TEnv.lookup_set_self (ρ : TEnv) (x : Var) (r : Ref) :
    TEnv.lookup (TEnv.set ρ x r) x = some r := by
  simp [TEnv.set]

/-- A binding of another name leaves the lookup alone. -/
theorem TEnv.lookup_set_of_ne {ρ : TEnv} {x y : Var} (h : x ≠ y) (r : Ref) :
    TEnv.lookup (TEnv.set ρ x r) y = TEnv.lookup ρ y := by
  simp [TEnv.set, TEnv.lookup, h]

/-- The environment an arm's binders extend: the binders are paired with the
references in order, the pairing of the last binder first, so a name an arm binds
twice takes the later pairing — the reading `Scidonia.RC.Pure`'s arm substitution
has of a repeated binder. -/
def TEnv.bindAll (ρ : TEnv) (ys : List Var) (rs : List Ref) : TEnv := (ys.zip rs).reverse ++ ρ

/-- A pair of a zipped list names a variable of its first list. -/
theorem mem_fst_of_mem_zip {ys : List Var} {rs : List Ref} {p : Var × Ref}
    (h : p ∈ ys.zip rs) : p.1 ∈ ys := by
  induction ys generalizing rs with
  | nil => simp at h
  | cons y ys ih =>
      cases rs with
      | nil => simp at h
      | cons r rs =>
          rw [List.zip_cons_cons] at h
          rcases List.mem_cons.mp h with heq | hmem
          · rw [heq]; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih hmem)

/-- Prepending pairs to an environment leaves the lookup of a name none of them
carries alone. -/
theorem TEnv.lookup_append_of_not_mem {l ρ : TEnv} {y : Var}
    (h : ∀ p ∈ l, p.1 ≠ y) : TEnv.lookup (l ++ ρ) y = TEnv.lookup ρ y := by
  induction l with
  | nil => rfl
  | cons p t ih =>
      obtain ⟨y', r'⟩ := p
      rw [List.cons_append, TEnv.lookup_cons_of_ne (h (y', r') (by simp)), ih]
      intro q hq
      exact h q (by simp [hq])

/-- A binder the environment does not name leaves the lookup alone. -/
theorem TEnv.lookup_bindAll_of_not_mem {ρ : TEnv} {ys : List Var} {rs : List Ref} {y : Var}
    (h : y ∉ ys) : TEnv.lookup (TEnv.bindAll ρ ys rs) y = TEnv.lookup ρ y := by
  refine TEnv.lookup_append_of_not_mem fun p hp => ?_
  have hp' : p ∈ ys.zip rs := List.mem_reverse.mp hp
  exact fun hh => h (hh ▸ mem_fst_of_mem_zip hp')

/-- The term's own multiplicities: one pair per occurrence the term holds, the
variable it was read at and the reference it names. -/
abbrev Multi := List (Var × Ref)

/-- The references a multiplicity list holds, one per occurrence: the term's own
side of the count `Counted` is stated at. The tags are not read here. -/
def expand (m : Multi) : List Ref := m.map (fun p => p.2)

/-- An empty multiplicity list contributes no reference. -/
@[simp] theorem expand_nil : expand ([] : Multi) = [] := rfl

/-- A multiplicity list contributes its first pair's reference before the rest. -/
@[simp] theorem expand_cons (p : Var × Ref) (m : Multi) : expand (p :: m) = p.2 :: expand m := rfl

/-- The multiplicity a `dup` step leaves: the occurrence the instruction supplies
joins the term's own, tagged with the variable it was read at. -/
def Multi.insert (m : Multi) (x : Var) (r : Ref) : Multi := (x, r) :: m

/-- The occurrence a `dup` supplies is the first of the list it leaves. -/
@[simp] theorem expand_insert (m : Multi) (x : Var) (r : Ref) :
    expand (Multi.insert m x r) = r :: expand m := rfl

/-- The multiplicity a `drop` step leaves: the occurrence the instruction consumes
leaves the term's own — the pair of the variable the instruction is stated at and
the reference the environment names for it. The pair is removed by its variable as
well as its reference, which is what makes the removal the term's own occurrence
rather than the first pair that happens to name the reference. -/
def Multi.dropOcc : Multi → Var → Ref → Multi
  | [], _, _ => []
  | (x, r') :: t, y, r => if (x, r') = (y, r) then t else (x, r') :: Multi.dropOcc t y r

/-- The occurrence a `drop` consumes is one the reference's count falls by: the
pair the term held is the one the instruction removes. -/
theorem expand_dropOcc_count_self (m : Multi) (y : Var) {r : Ref} (hmem : (y, r) ∈ m) :
    (expand (Multi.dropOcc m y r)).count r + 1 = (expand m).count r := by
  induction m with
  | nil => simp at hmem
  | cons p t ih =>
      obtain ⟨x, s⟩ := p
      have hmem' : (y, r) = (x, s) ∨ (y, r) ∈ t := List.mem_cons.mp hmem
      by_cases h : (x, s) = (y, r)
      · have hdrop : Multi.dropOcc ((x, s) :: t) y r = t := by simp [Multi.dropOcc, h]
        rw [hdrop, expand_cons, h, List.count_cons_self]
      · have hdrop : Multi.dropOcc ((x, s) :: t) y r = (x, s) :: Multi.dropOcc t y r := by
          simp [Multi.dropOcc, h]
        rw [hdrop, expand_cons, expand_cons]
        have ht : (y, r) ∈ t := by
          rcases hmem' with heq | ht
          · exact absurd heq.symm h
          · exact ht
        have hi := ih ht
        by_cases hs : s = r
        · subst hs
          rw [List.count_cons_self, List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne hs, List.count_cons_of_ne hs]
          exact hi

/-- A `drop` at one name leaves another name's reference's count alone: the pair it
removes names the reference it was stated at. -/
theorem expand_dropOcc_count_of_ne (m : Multi) (y : Var) {r s : Ref} (h : s ≠ r) :
    (expand (Multi.dropOcc m y r)).count s = (expand m).count s := by
  induction m with
  | nil => rfl
  | cons p t ih =>
      obtain ⟨x, s'⟩ := p
      by_cases hp : (x, s') = (y, r)
      · have hdrop : Multi.dropOcc ((x, s') :: t) y r = t := by simp [Multi.dropOcc, hp]
        have hs' : s' = r := congrArg Prod.snd hp
        have hne : s' ≠ s := fun hh => h (hh.symm.trans hs')
        rw [hdrop, expand_cons, List.count_cons_of_ne hne]
      · have hdrop : Multi.dropOcc ((x, s') :: t) y r = (x, s') :: Multi.dropOcc t y r := by
          simp [Multi.dropOcc, hp]
        rw [hdrop, expand_cons, expand_cons]
        by_cases hs : s' = s
        · rw [hs, List.count_cons_self, List.count_cons_self, ih]
        · rw [List.count_cons_of_ne hs, List.count_cons_of_ne hs]
          exact ih

/-- A `drop` leaves only pairs of the multiplicity it was handed. -/
theorem mem_dropOcc {p : Var × Ref} {m : Multi} {y : Var} {r : Ref}
    (h : p ∈ Multi.dropOcc m y r) : p ∈ m := by
  induction m with
  | nil => simp [Multi.dropOcc] at h
  | cons q t ih =>
      obtain ⟨x, s⟩ := q
      by_cases hq : (x, s) = (y, r)
      · have hdrop : Multi.dropOcc ((x, s) :: t) y r = t := by simp [Multi.dropOcc, hq]
        rw [hdrop] at h
        exact List.mem_cons_of_mem _ h
      · have hdrop : Multi.dropOcc ((x, s) :: t) y r = (x, s) :: Multi.dropOcc t y r := by
          simp [Multi.dropOcc, hq]
        rw [hdrop, List.mem_cons] at h
        rcases h with heq | hmem
        · rw [heq]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih hmem)

/-! ## The slot a store installs

A store at slot `i` of the cell at hand installs the cell's own slots with slot `i`
set to the value's reference. `setAt` leaves a list shorter than the index as it
is, which is why a store's rule asks for the index to be one of the cell's slots. -/

/-- The list with its element at `i` replaced by `x`. A list shorter than the index
is returned unchanged. -/
def setAt : List Ref → Nat → Ref → List Ref
  | [], _, _ => []
  | _ :: t, 0, x => x :: t
  | y :: t, n + 1, x => y :: setAt t n x

/-- An empty list has no element to replace. -/
@[simp] theorem setAt_nil (i : Nat) (x : Ref) : setAt ([] : List Ref) i x = [] := by
  cases i <;> rfl

/-- Replacing the head replaces it. -/
@[simp] theorem setAt_zero (y : Ref) (t : List Ref) (x : Ref) : setAt (y :: t) 0 x = x :: t := rfl

/-- Replacing past the head keeps the head and replaces in the tail. -/
@[simp] theorem setAt_succ (y : Ref) (t : List Ref) (n : Nat) (x : Ref) :
    setAt (y :: t) (n + 1) x = y :: setAt t n x := rfl

/-- The slots a store at the cell `r`'s slot `i` installs: the cell's own slots with
slot `i` set to the value's reference. -/
def storeSlots (c : CHeap) (r : Ref) (i : Nat) (wv : Ref) : List Ref :=
  setAt (CHeap.slotsAt c r) i wv

/-! ## The checks

The tests the schema makes before an operation runs: a reference is a live cell, a
write's operand names live cells and neither the cell it writes nor one of that
cell's own slots, and a match's arm rebinds none of the names the term's
multiplicities hold. -/

/-- Whether a reference is a live cell of the heap. -/
def live (c : CHeap) (r : Ref) : Bool := decide (r ∈ CHeap.refs c)

/-- The liveness check passing is the membership it tests. -/
theorem live_eq_true {c : CHeap} {r : Ref} (h : live c r = true) : r ∈ CHeap.refs c := by
  unfold live at h
  exact of_decide_eq_true h

/-- The check a write's operand has to pass at the cell it writes: every reference
the written slots name is a live cell, the slots do not name the cell itself, and
that cell's own slots do not name it either. -/
def writeCheck (c : CHeap) (r : Ref) (ks : List Ref) : Bool :=
  ks.all (fun x => decide (x ∈ CHeap.refs c)) && decide (r ∉ ks)
    && decide (r ∉ CHeap.slotsAt c r)

/-- A write whose check passes names live cells only. -/
theorem writeCheck_live {c : CHeap} {r : Ref} {ks : List Ref} (h : writeCheck c r ks = true) :
    ∀ x ∈ ks, x ∈ CHeap.refs c := by
  intro x hx
  rw [writeCheck, Bool.and_eq_true_iff, Bool.and_eq_true_iff] at h
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h.1.1 x hx)

/-- A write whose check passes does not name the cell it writes. -/
theorem writeCheck_avoids {c : CHeap} {r : Ref} {ks : List Ref} (h : writeCheck c r ks = true) :
    r ∉ ks := by
  rw [writeCheck, Bool.and_eq_true_iff, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true h.1.2

/-- A write whose check passes lands at a cell whose own slots do not name it. -/
theorem writeCheck_self {c : CHeap} {r : Ref} {ks : List Ref} (h : writeCheck c r ks = true) :
    r ∉ CHeap.slotsAt c r := by
  rw [writeCheck, Bool.and_eq_true_iff, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true h.2

/-- Whether the term's multiplicities name none of an arm's binders: the check a
match makes before the arm rebinds them. -/
def freeOf (m : Multi) (ys : List Var) : Bool := m.all (fun p => decide (p.1 ∉ ys))

/-- A match whose check passes rebinds none of the names the term holds. -/
theorem freeOf_eq_true {m : Multi} {ys : List Var} (h : freeOf m ys = true) :
    ∀ p ∈ m, p.1 ∉ ys := by
  intro p hp
  rw [freeOf, List.all_eq_true] at h
  exact of_decide_eq_true (h p hp)

/-- Whether the term's own account holds a name only at one reference: the check a
binding of a variable makes before it takes the name over. The name reads the bound
reference from then on, so an occurrence the account still held at another reference
would name the wrong cell. -/
def nameOnly (m : Multi) (x : Var) (r : Ref) : Bool :=
  m.all (fun p => decide (p.1 ≠ x) || decide (p.2 = r))

/-- A check that passes holds a name only at the reference it was asked about. -/
theorem nameOnly_eq_true {m : Multi} {x : Var} {r : Ref} (h : nameOnly m x r = true) :
    ∀ p ∈ m, p.1 = x → p.2 = r := by
  intro p hp hx
  rw [nameOnly, List.all_eq_true] at h
  rcases Bool.or_eq_true_iff.mp (h p hp) with hne | heq
  · exact absurd hx (of_decide_eq_true hne)
  · exact of_decide_eq_true heq

/-- Whether the term's own account holds a name at all: the check a binding of an
allocated value makes before it takes the name over. The cell's reference is fresh,
so an occurrence of the name at any reference would be read at the new binding. -/
def freeName (m : Multi) (x : Var) : Bool :=
  m.all (fun p => decide (p.1 ≠ x))

/-- A check that passes holds no occurrence of the name it was asked about. -/
theorem freeName_eq_true {m : Multi} {x : Var} (h : freeName m x = true) :
    ∀ p ∈ m, p.1 ≠ x := by
  intro p hp
  rw [freeName, List.all_eq_true] at h
  exact of_decide_eq_true (h p hp)

/-- Whether the term's own account holds a name no longer, once the occurrence the
instruction consumes has left it: the check a copying store makes before it rebinds
the subject's name. The name reads the fresh location from then on, so an occurrence
the account still held would be read at the new location. -/
def nameGone (m : Multi) (y : Var) (r : Ref) : Bool :=
  (Multi.dropOcc m y r).all (fun p => decide (p.1 ≠ y))

/-- A check that passes holds no occurrence of the name it was asked about, once the
consumed occurrence has left the account. -/
theorem nameGone_eq_true {m : Multi} {y : Var} {r : Ref} (h : nameGone m y r = true) :
    ∀ p ∈ Multi.dropOcc m y r, p.1 ≠ y := by
  intro p hp
  rw [nameGone, List.all_eq_true] at h
  exact of_decide_eq_true (h p hp)

/-! ## The term's own account at an instruction

Which occurrence an instruction consumes is a statement about the term and not
about a count: `Owns` reads the pair of the variable the current expression's
instruction reads and the reference the environment names for it out of the term's
own multiplicities. It is indexed by the expression, so it states what the
multiplicities are *of the term in hand*, and it is the premise a rule's occurrence
comes from — `Scidonia.RC.Ownership` states it as a hypothesis of the two store
results. -/

/-- The term's own account at the current expression: the expression's instruction
reads an occurrence out of the term's own multiplicities, so the account holds the
pair of the variable it reads and the reference the environment names for it. One
constructor per instruction that consumes an occurrence — a `dup` supplies one
rather than reading it, and a match reads its cell's slots off the heap rather than
out of the term's own list — and a binding's constructors carry the condition its
name makes: an occurrence of the name the account still held at another reference
would be read at the bound reference. -/
inductive Owns (ρ : TEnv) : Multi → Expr → Prop where
  /-- A `drop` reads the occurrence it releases out of the term's own account. -/
  | drop {m : Multi} {y : Var} {r : Ref} {e : Expr} (hρ : ρ.lookup y = some r)
      (hmem : (y, r) ∈ m) : Owns ρ m (.drop y e)
  /-- A binding of a variable reads the occurrence its bound variable names out of
  the term's own account, and holds the binder only at the bound reference. -/
  | bindVar {m : Multi} {x z : Var} {r : Ref} {e₂ : Expr} (hρ : ρ.lookup z = some r)
      (hmem : (z, r) ∈ m) (hheld : ∀ p ∈ m, p.1 = x → p.2 = r) :
      Owns ρ m (.bind x (.var z) e₂)
  /-- An application of an abstraction to a variable reads the occurrence the
  argument names out of the term's own account, the function position being an
  abstraction the step has already reached. -/
  | appVar {m : Multi} {x z : Var} {r : Ref} {body : Expr} (hρ : ρ.lookup z = some r)
      (hmem : (z, r) ∈ m) (hheld : ∀ p ∈ m, p.1 = x → p.2 = r) :
      Owns ρ m (.app (.lam x body) (.var z))
  /-- A store reads the occurrence its subject names out of the term's own
  account. -/
  | store {m : Multi} {y : Var} {r : Ref} {i : Nat} {v : Expr} (hρ : ρ.lookup y = some r)
      (hmem : (y, r) ∈ m) : Owns ρ m (.store (.var y) i v)

/-- The term's own account of a store holds the occurrence the subject names: the
pair of the subject's variable and the reference the environment names for it is one
the account holds. -/
theorem Owns.store_occurrence {ρ : TEnv} {m : Multi} {y : Var} {i : Nat} {v : Expr}
    (h : Owns ρ m (.store (.var y) i v)) : ∃ r, ρ.lookup y = some r ∧ (y, r) ∈ m := by
  cases h with
  | store hρ hmem => exact ⟨_, hρ, hmem⟩

/-! ## A value's reference, realised on the heap

The configuration's term has no form for a location, so a value position that holds
a node construction or an abstraction is turned into a reference by a step of its
own: the cell is allocated at the heap's fresh location, its slots are the fields'
references, and a closure holds no slots. A variable's reference is the one the
environment binds it to. -/

/-- The state a fresh cell with the slots `ks` is allocated in: `RCHeap.alloc`'s two
projections at the heap's own fresh location. -/
def allocWith (c : CHeap) (hs : List Ref) (ks : List Ref) : CHeap × List Ref :=
  alloc c hs (fresh c ks) ks

/-- The heap a fresh cell with the slots `ks` is allocated on. -/
@[simp] theorem allocWith_fst (c : CHeap) (hs : List Ref) (ks : List Ref) :
    (allocWith c hs ks).1 = (alloc c hs (fresh c ks) ks).1 := rfl

/-- The handles a fresh cell with the slots `ks` is allocated with. -/
@[simp] theorem allocWith_snd (c : CHeap) (hs : List Ref) (ks : List Ref) :
    (allocWith c hs ks).2 = (alloc c hs (fresh c ks) ks).2 := rfl

/-- A value realised on the heap: the state the value's reference is read in, the
reference, and the cell a node or a closure was allocated at. -/
inductive ValRef : CHeap → List Ref → TEnv → Expr → CHeap → List Ref → Ref → Prop where
  /-- A variable names the reference the environment binds it to, which is a live
  cell. -/
  | var {c : CHeap} {hs : List Ref} {ρ : TEnv} {x : Var} {r : Ref}
      (h : ρ.lookup x = some r) (hlive : r ∈ CHeap.refs c) : ValRef c hs ρ (.var x) c hs r
  /-- An abstraction realises a cell holding no slots: the model's closures capture
  nothing, and the body reads its free variables from the environment in force. -/
  | lam {c : CHeap} {hs : List Ref} {ρ : TEnv} {x : Var} {body : Expr} :
      ValRef c hs ρ (.lam x body) (allocWith c hs []).1 (allocWith c hs []).2 (fresh c [])
  /-- A nullary node realises a fresh cell holding no slots. -/
  | con0 {c : CHeap} {hs : List Ref} {ρ : TEnv} {ctag : Ctor} :
      ValRef c hs ρ (.con0 ctag) (allocWith c hs []).1 (allocWith c hs []).2 (fresh c [])
  /-- A unary node realises a fresh cell whose one slot is its field's
  reference. -/
  | con1 {c : CHeap} {hs : List Ref} {ρ : TEnv} {ctag : Ctor} {a : Expr} {c₁ : CHeap}
      {hs₁ : List Ref} {r₁ : Ref} (h : ValRef c hs ρ a c₁ hs₁ r₁)
      (hlive : r₁ ∈ CHeap.refs c₁) :
      ValRef c hs ρ (.con1 ctag a) (allocWith c₁ hs₁ [r₁]).1 (allocWith c₁ hs₁ [r₁]).2
        (fresh c₁ [r₁])
  /-- A binary node realises a fresh cell whose two slots are its fields'
  references, realised in order. -/
  | con2 {c : CHeap} {hs : List Ref} {ρ : TEnv} {ctag : Ctor} {a b : Expr} {c₁ : CHeap}
      {hs₁ : List Ref} {r₁ : Ref} {c₂ : CHeap} {hs₂ : List Ref} {r₂ : Ref}
      (h₁ : ValRef c hs ρ a c₁ hs₁ r₁) (h₂ : ValRef c₁ hs₁ ρ b c₂ hs₂ r₂)
      (hlive₁ : r₁ ∈ CHeap.refs c₂) (hlive₂ : r₂ ∈ CHeap.refs c₂) :
      ValRef c hs ρ (.con2 ctag a b) (allocWith c₂ hs₂ [r₁, r₂]).1 (allocWith c₂ hs₂ [r₁, r₂]).2
        (fresh c₂ [r₁, r₂])

/-! ## The step relation

One rule per instruction, one rule per position λ¹'s heap semantics reaches, and
the rules that read the term's own occurrences require that the term holds the
occurrence they consume: the pair of the variable the instruction reads and the
reference the environment names for it. -/

/-- A step of the target runtime: the heap, the handles held outside the term, the
environment, the term's multiplicities and the term, and what the instruction
leaves of each.

* `dup y; e` performs the runtime's increment at the cell `y` names and adds the
  occurrence it supplies to the term's own.
* `drop y; e` performs the runtime's non-final decrement at a cell of count two or
  more, and the runtime's final release at a cell of count one, and takes the
  occurrence the term held out of its own list. The occurrence is what the rule
  requires: a `drop` of a pair the term does not hold is not a step, which is the
  shape the lowering's `surplus` emits.
* `val x = v; e₂` binds `x` to the value's reference. At a variable the heap and
  the run's handles are what they were — the variable's own occurrence becomes the
  binder's, which is why the rule requires that occurrence to be one the term
  holds — and the binder's name has to be one the account holds only at the bound
  reference, because it reads that reference from then on. At an allocated value
  the realization allocates the cell and hands out its handle, which the binder
  takes up in place of the occurrence it adds.
* `(λx. body) v` resumes the body with `x` bound to the argument's reference, in
  the same two shapes.
* `match (var z) { c ȳ → body }` binds the arm's binders to the slots of the cell
  `z` names, in order, and resumes the body; the cell's tag is not read, and the
  rule requires the binders to shadow none of the names the term holds.
* `store (var y) i v` is `RCHeap.update` at the cell `y` names, with the cell's
  slots `i` set to the value's reference, at the handles the run holds plus the
  term's own occurrences. At a count of one it is destructive and leaves the
  multiplicity and the handles alone — the write's result names the cell it wrote.
  Otherwise it copies: the binder names the fresh location, the occurrence of the
  name the term held leaves its own list — the name reads the fresh location from
  then on, so the account must hold no other occurrence of it — and the run's
  handles stay as they were.
* A step in one of the positions the term's evaluation reaches: the function
  position of an application, its argument position while the function is a value,
  the right-hand side of a binding, and the fields of a node construction, the
  second field of a binary node once the first is a value — the order `ValRef`
  realizes the fields in. The rule below each carries the position's step and
  leaves the heap, the handles, the environment and the multiplicities where the
  position's step left them. -/
inductive TStep :
    CHeap → List Ref → TEnv → Multi → Expr → CHeap → List Ref → TEnv → Multi → Expr → Prop where
  /-- The runtime's increment at a live cell, and the occurrence it supplies. -/
  | dup {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {r : Ref} {e : Expr}
      (hρ : ρ.lookup y = some r) (hlive : r ∈ CHeap.refs c) :
      TStep c hs ρ m (.dup y e) (dup c hs r).1 hs ρ (Multi.insert m y r) e
  /-- The runtime's non-final decrement at a cell of count two or more, and the
  occurrence the term held. -/
  | dropShared {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {r : Ref}
      {e : Expr} (hρ : ρ.lookup y = some r) (h2 : 2 ≤ CHeap.count c r)
      (hsub : (y, r) ∈ m) :
      TStep c hs ρ m (.drop y e) (decRef c hs r).1 hs ρ (Multi.dropOcc m y r) e
  /-- The runtime's final release at a cell of count one, and the occurrence the
  term held. -/
  | dropFinal {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {r : Ref}
      {e : Expr} (hρ : ρ.lookup y = some r) (h1 : CHeap.count c r = 1)
      (hsub : (y, r) ∈ m) :
      TStep c hs ρ m (.drop y e) (release c hs r).1 hs ρ (Multi.dropOcc m y r) e
  /-- A binding whose bound term is a variable: the heap and the run's handles are
  what they were, and the variable's own occurrence becomes the binder's. The rule
  requires that occurrence to be one the term holds, which is the reading of a use
  of a variable, and it requires the binder's name to be one the account holds
  nowhere but at that occurrence's reference. -/
  | bindVar {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x z : Var} {e₂ : Expr}
      {r : Ref} (hρ : ρ.lookup z = some r) (hsub : (z, r) ∈ m)
      (hhigh : nameOnly m x r = true) :
      TStep c hs ρ m (.bind x (.var z) e₂) c hs (TEnv.set ρ x r)
        (Multi.insert (Multi.dropOcc m z r) x r) e₂
  /-- A binding whose bound term is an allocated value: the value is realised and
  the binder takes up the reference the realization handed out, so the allocated
  cell is named by the binder's occurrence where it was named by the realization's
  handle, and the binder's name holds no occurrence of the account at another
  reference. -/
  | bindVal {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x : Var} {v e₂ : Expr}
      {c' : CHeap} {hs' : List Ref} {r : Ref} (hv : ValRef c hs ρ v c' hs' r)
      (halloc : ∀ z, v ≠ .var z) (hfree : freeName m x = true) :
      TStep c hs ρ m (.bind x v e₂) c' (dropHandle hs' r) (TEnv.set ρ x r)
        (Multi.insert m x r) e₂
  /-- An application of an abstraction whose argument is a variable: the body
  resumes with the parameter bound to the variable's occurrence. -/
  | appVar {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x z : Var} {body : Expr}
      {r : Ref} (hρ : ρ.lookup z = some r) (hsub : (z, r) ∈ m)
      (hhigh : nameOnly m x r = true) :
      TStep c hs ρ m (.app (.lam x body) (.var z)) c hs (TEnv.set ρ x r)
        (Multi.insert (Multi.dropOcc m z r) x r) body
  /-- An application of an abstraction whose argument is an allocated value. The
  parameter's name holds no occurrence of the account at another reference. -/
  | appVal {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x : Var} {body v : Expr}
      {c' : CHeap} {hs' : List Ref} {r : Ref} (hv : ValRef c hs ρ v c' hs' r)
      (halloc : ∀ z, v ≠ .var z) (hfree : freeName m x = true) :
      TStep c hs ρ m (.app (.lam x body) v) c' (dropHandle hs' r) (TEnv.set ρ x r)
        (Multi.insert m x r) body
  /-- A match on the cell a variable names: the arm's binders receive the cell's
  slots and the body resumes. -/
  | matchC {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {z : Var} {ctag : Ctor}
      {ys : List Var} {body : Expr} {r : Ref} (hρ : ρ.lookup z = some r)
      (hlen : ys.length = (CHeap.slotsAt c r).length) (hfree : ∀ p ∈ m, p.1 ∉ ys) :
      TStep c hs ρ m (.matchC (.var z) ctag ys body) c hs
        (TEnv.bindAll ρ ys (CHeap.slotsAt c r)) m body
  /-- A store at a cell of count one: the destructive branch of `RCHeap.update`, at
  the cell the subject names, with the multiplicity and the handles left alone. The
  rule requires the subject's occurrence to be one the term holds. -/
  | storeExclusive {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {i : Nat}
      {v : Expr} {c₁ : CHeap} {hs₁ : List Ref} {wv r : Ref} (hρ : ρ.lookup y = some r)
      (hv : ValRef c hs ρ v c₁ hs₁ wv) (hi : i < (CHeap.slotsAt c₁ r).length)
      (hchk : writeCheck c₁ r (storeSlots c₁ r i wv) = true) (h1 : CHeap.count c₁ r = 1)
      (hsub : (y, r) ∈ m) :
      TStep c hs ρ m (.store (.var y) i v)
        (update c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv)).1 hs₁ ρ m (.var y)
  /-- A store at a cell of count other than one: the copying branch of
  `RCHeap.update`, which lands the written slots at a fresh location, leaves the old
  cell its slots and one reference fewer, and rebinds the subject to the fresh
  location at one occurrence of the old reference fewer. The rule requires the
  subject's occurrence to be one the term holds and its name to be one the account
  then holds nowhere, because the name reads the fresh location. -/
  | storeShared {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {i : Nat}
      {v : Expr} {c₁ : CHeap} {hs₁ : List Ref} {wv r : Ref} (hρ : ρ.lookup y = some r)
      (hv : ValRef c hs ρ v c₁ hs₁ wv) (hi : i < (CHeap.slotsAt c₁ r).length)
      (hchk : writeCheck c₁ r (storeSlots c₁ r i wv) = true) (hsub : (y, r) ∈ m)
      (hgone : nameGone m y r = true) (h2 : CHeap.count c₁ r ≠ 1) :
      TStep c hs ρ m (.store (.var y) i v)
        (update c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv)).1 hs₁
        (TEnv.set ρ y (fresh c₁ (storeSlots c₁ r i wv)))
        (Multi.insert (Multi.dropOcc m y r) y (fresh c₁ (storeSlots c₁ r i wv))) (.var y)
  /-- A step in the right-hand side of a binding: the binding is left where it is
  and the configuration the position's step leaves is the one the binding continues
  from. The lowering puts the instructions its differential demands there, so a
  binding's right-hand side is a computation whenever it is not a value. -/
  | bindRhs {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x : Var} {e₁ e₂ : Expr}
      {c' : CHeap} {hs' : List Ref} {ρ' : TEnv} {m' : Multi} {e₁' : Expr}
      (h : TStep c hs ρ m e₁ c' hs' ρ' m' e₁') :
      TStep c hs ρ m (.bind x e₁ e₂) c' hs' ρ' m' (.bind x e₁' e₂)
  /-- A step in the function position of an application. -/
  | appFun {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {f a : Expr} {c' : CHeap}
      {hs' : List Ref} {ρ' : TEnv} {m' : Multi} {f' : Expr}
      (h : TStep c hs ρ m f c' hs' ρ' m' f') :
      TStep c hs ρ m (.app f a) c' hs' ρ' m' (.app f' a)
  /-- A step in the argument of an application whose function is a value, which is
  the source's own condition for that position. -/
  | appArg {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {f a : Expr} {c' : CHeap}
      {hs' : List Ref} {ρ' : TEnv} {m' : Multi} {a' : Expr} (hf : Value f)
      (h : TStep c hs ρ m a c' hs' ρ' m' a') :
      TStep c hs ρ m (.app f a) c' hs' ρ' m' (.app f a')
  /-- A step in the field of a unary node. -/
  | con1Field {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {ct : Ctor} {a : Expr}
      {c' : CHeap} {hs' : List Ref} {ρ' : TEnv} {m' : Multi} {a' : Expr}
      (h : TStep c hs ρ m a c' hs' ρ' m' a') :
      TStep c hs ρ m (.con1 ct a) c' hs' ρ' m' (.con1 ct a')
  /-- A step in the first field of a binary node. -/
  | con2FieldL {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {ct : Ctor} {a b : Expr}
      {c' : CHeap} {hs' : List Ref} {ρ' : TEnv} {m' : Multi} {a' : Expr}
      (h : TStep c hs ρ m a c' hs' ρ' m' a') :
      TStep c hs ρ m (.con2 ct a b) c' hs' ρ' m' (.con2 ct a' b)
  /-- A step in the second field of a binary node, which the realization reaches
  once the first field is a value. -/
  | con2FieldR {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {ct : Ctor} {a b : Expr}
      {c' : CHeap} {hs' : List Ref} {ρ' : TEnv} {m' : Multi} {b' : Expr} (ha : Value a)
      (h : TStep c hs ρ m b c' hs' ρ' m' b') :
      TStep c hs ρ m (.con2 ct a b) c' hs' ρ' m' (.con2 ct a b')

/-! ## The evaluation contexts

The contexts λ¹'s heap semantics reaches, as terms with one hole: the function
position of an application, its argument position while the function is a value,
the right-hand side of a binding, and the fields of a node construction. The
congruence rules above are these contexts one by one, which `tstep_of_plug` states:
a step inside a well-formed context is a step of the relation. -/

/-- An evaluation context of the target: a term with one hole, in the positions a
step of the relation reaches. -/
inductive TCtx where
  /-- The hole. -/
  | hole
  /-- `E a`, the function position of an application. -/
  | appL (E : TCtx) (a : Expr)
  /-- `f E`, the argument position of an application. -/
  | appR (f : Expr) (E : TCtx)
  /-- `val x = E; e₂`, the right-hand side of a binding. -/
  | bindL (x : Var) (E : TCtx) (e₂ : Expr)
  /-- `C E`, the field of a unary node. -/
  | con1L (ct : Ctor) (E : TCtx)
  /-- `C E b`, the first field of a binary node. -/
  | con2L (ct : Ctor) (E : TCtx) (b : Expr)
  /-- `C a E`, the second field of a binary node. -/
  | con2R (ct : Ctor) (a : Expr) (E : TCtx)

/-- A context's hole filled with a term. -/
def TCtx.plug : TCtx → Expr → Expr
  | .hole, e => e
  | .appL E a, e => .app (E.plug e) a
  | .appR f E, e => .app f (E.plug e)
  | .bindL x E e₂, e => .bind x (E.plug e) e₂
  | .con1L ct E, e => .con1 ct (E.plug e)
  | .con2L ct E b, e => .con2 ct (E.plug e) b
  | .con2R ct a E, e => .con2 ct a (E.plug e)

/-- The contexts whose surrounding terms are values where a rule requires one:
stepping an application's argument needs the function to be a value, and stepping a
binary node's second field needs the first field to be one — the order `ValRef`
realizes the fields in. -/
inductive TCtx.WF : TCtx → Prop where
  /-- The hole is well formed. -/
  | hole : WF .hole
  /-- The function position of an application may hold any context. -/
  | appL {E a} : WF E → WF (.appL E a)
  /-- The argument position of an application requires a value function. -/
  | appR {f E} : Value f → WF E → WF (.appR f E)
  /-- The right-hand side of a binding may hold any context. -/
  | bindL {x E e₂} : WF E → WF (.bindL x E e₂)
  /-- The field of a unary node may hold any context. -/
  | con1L {ct E} : WF E → WF (.con1L ct E)
  /-- The first field of a binary node may hold any context. -/
  | con2L {ct E b} : WF E → WF (.con2L ct E b)
  /-- The second field of a binary node requires a value first field. -/
  | con2R {ct a E} : Value a → WF E → WF (.con2R ct a E)

/-- A step inside a well-formed context is a step of the relation: the congruence
rules above read as the contexts they are, one per context former. -/
theorem tstep_of_plug : ∀ {E : TCtx} {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi}
    {r e' : Expr} {c' : CHeap} {hs' : List Ref} {ρ' : TEnv} {m' : Multi},
    TCtx.WF E → TStep c hs ρ m r c' hs' ρ' m' e' →
      TStep c hs ρ m (E.plug r) c' hs' ρ' m' (E.plug e') := by
  intro E
  induction E with
  | hole => intro c hs ρ m r e' c' hs' ρ' m' _ h; exact h
  | appL E a ih =>
      intro c hs ρ m r e' c' hs' ρ' m' hwf h
      cases hwf with
      | appL hw => exact TStep.appFun (ih hw h)
  | appR f E ih =>
      intro c hs ρ m r e' c' hs' ρ' m' hwf h
      cases hwf with
      | appR hf hw => exact TStep.appArg hf (ih hw h)
  | bindL x E e₂ ih =>
      intro c hs ρ m r e' c' hs' ρ' m' hwf h
      cases hwf with
      | bindL hw => exact TStep.bindRhs (ih hw h)
  | con1L ct E ih =>
      intro c hs ρ m r e' c' hs' ρ' m' hwf h
      cases hwf with
      | con1L hw => exact TStep.con1Field (ih hw h)
  | con2L ct E b ih =>
      intro c hs ρ m r e' c' hs' ρ' m' hwf h
      cases hwf with
      | con2L hw => exact TStep.con2FieldL (ih hw h)
  | con2R ct a E ih =>
      intro c hs ρ m r e' c' hs' ρ' m' hwf h
      cases hwf with
      | con2R ha hw => exact TStep.con2FieldR ha (ih hw h)

/-! ## The evaluator

The same rules as functions: the rule the configuration's root takes, the search of
the positions the term's evaluation reaches, and the fuel-indexed iteration. `claim?`
realises a value's reference; `troot?` performs the instruction rule the whole term
takes, answering `none` where none applies at the root; and `tstep?` answers that
where it applies and otherwise the step the position search reaches, which is the
step the relation's congruence rules are. -/

/-- A value's reference, realised on the heap: `none` when a variable the value
reads is unbound or a reference it names is not a live cell. A node's cell is
allocated at the heap's fresh location with the fields' references as its slots,
and a closure's cell holds no slots. -/
def claim? : CHeap → List Ref → TEnv → Expr → Option (CHeap × List Ref × Ref)
  | c, hs, ρ, .var x =>
      match ρ.lookup x with
      | none => none
      | some r => if live c r then some (c, hs, r) else none
  | c, hs, _, .lam _ _ => some ((allocWith c hs []).1, (allocWith c hs []).2, fresh c [])
  | c, hs, _, .con0 _ => some ((allocWith c hs []).1, (allocWith c hs []).2, fresh c [])
  | c, hs, ρ, .con1 _ a =>
      match claim? c hs ρ a with
      | none => none
      | some (c₁, hs₁, r₁) =>
          if live c₁ r₁ then
            some ((allocWith c₁ hs₁ [r₁]).1, (allocWith c₁ hs₁ [r₁]).2, fresh c₁ [r₁])
          else none
  | c, hs, ρ, .con2 _ a b =>
      match claim? c hs ρ a with
      | none => none
      | some (c₁, hs₁, r₁) =>
          match claim? c₁ hs₁ ρ b with
          | none => none
          | some (c₂, hs₂, r₂) =>
              if live c₂ r₁ && live c₂ r₂ then
                some ((allocWith c₂ hs₂ [r₁, r₂]).1, (allocWith c₂ hs₂ [r₁, r₂]).2,
                  fresh c₂ [r₁, r₂])
              else none
  | _, _, _, _ => none

/-- The instruction rule the configuration takes at its own root, or `none` where
no rule applies to the whole term: the rules of `TStep` whose redex is the term
itself, with the checks their premises make. `tstep?` answers this where it
applies and otherwise searches the positions the term's evaluation reaches. -/
def troot? :
    CHeap → List Ref → TEnv → Multi → Expr →
      Option (CHeap × List Ref × TEnv × Multi × Expr)
  | c, hs, ρ, m, .dup y e =>
      match ρ.lookup y with
      | none => none
      | some r => if live c r then some ((dup c hs r).1, hs, ρ, Multi.insert m y r, e) else none
  | c, hs, ρ, m, .drop y e =>
      match ρ.lookup y with
      | none => none
      | some r =>
          if (y, r) ∈ m then
            if CHeap.count c r = 1 then
              some ((release c hs r).1, hs, ρ, Multi.dropOcc m y r, e)
            else if 2 ≤ CHeap.count c r then
              some ((decRef c hs r).1, hs, ρ, Multi.dropOcc m y r, e)
            else none
          else none
  | c, hs, ρ, m, .bind x v e₂ =>
      match v with
      | .var z =>
          match ρ.lookup z with
          | none => none
          | some r =>
              if (z, r) ∈ m && nameOnly m x r then
                some (c, hs, TEnv.set ρ x r, Multi.insert (Multi.dropOcc m z r) x r, e₂)
              else none
      | _ =>
          if freeName m x then
            match claim? c hs ρ v with
            | none => none
            | some (c₁, hs₁, r) =>
                some (c₁, dropHandle hs₁ r, TEnv.set ρ x r, Multi.insert m x r, e₂)
          else none
  | c, hs, ρ, m, .app f a =>
      match f with
      | .lam x body =>
          match a with
          | .var z =>
              match ρ.lookup z with
              | none => none
              | some r =>
                  if (z, r) ∈ m && nameOnly m x r then
                    some (c, hs, TEnv.set ρ x r, Multi.insert (Multi.dropOcc m z r) x r, body)
                  else none
          | _ =>
              if freeName m x then
                match claim? c hs ρ a with
                | none => none
                | some (c₁, hs₁, r) =>
                    some (c₁, dropHandle hs₁ r, TEnv.set ρ x r, Multi.insert m x r, body)
              else none
      | _ => none
  | c, hs, ρ, m, .matchC s _ ys body =>
      match s with
      | .var z =>
          match ρ.lookup z with
          | none => none
          | some r =>
              if ys.length = (CHeap.slotsAt c r).length && freeOf m ys then
                some (c, hs, TEnv.bindAll ρ ys (CHeap.slotsAt c r), m, body)
              else none
      | _ => none
  | c, hs, ρ, m, .store s i v =>
      match s with
      | .var y =>
          match ρ.lookup y with
          | none => none
          | some r =>
              match claim? c hs ρ v with
              | none => none
              | some (c₁, hs₁, wv) =>
                  if i < (CHeap.slotsAt c₁ r).length
                      && writeCheck c₁ r (storeSlots c₁ r i wv) then
                    if CHeap.count c₁ r = 1 then
                      if (y, r) ∈ m then
                        some ((update c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv)).1, hs₁, ρ, m,
                          .var y)
                      else none
                    else if (y, r) ∈ m && nameGone m y r then
                      some ((update c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv)).1, hs₁,
                        TEnv.set ρ y (fresh c₁ (storeSlots c₁ r i wv)),
                        Multi.insert (Multi.dropOcc m y r) y (fresh c₁ (storeSlots c₁ r i wv)),
                        .var y)
                    else none
                  else none
      | _ => none
  | _, _, _, _, _ => none

/-- One instruction, or one step in a position the term's evaluation reaches, or
`none` where the configuration takes no step. The rule the configuration's root
takes is answered first, and where it takes none the positions are searched in the
order the semantics reaches them: a binding's right-hand side, an application's
function before its argument while the function is a value, and a binary node's
first field before its second. -/
def tstep? :
    CHeap → List Ref → TEnv → Multi → Expr →
      Option (CHeap × List Ref × TEnv × Multi × Expr)
  | c, hs, ρ, m, .bind x e₁ e₂ =>
      match troot? c hs ρ m (.bind x e₁ e₂) with
      | some cfg => some cfg
      | none =>
          match tstep? c hs ρ m e₁ with
          | some (c', hs', ρ', m', e₁') => some (c', hs', ρ', m', .bind x e₁' e₂)
          | none => none
  | c, hs, ρ, m, .app f a =>
      match troot? c hs ρ m (.app f a) with
      | some cfg => some cfg
      | none =>
          if valueB f then
            match tstep? c hs ρ m a with
            | some (c', hs', ρ', m', a') => some (c', hs', ρ', m', .app f a')
            | none => none
          else
            match tstep? c hs ρ m f with
            | some (c', hs', ρ', m', f') => some (c', hs', ρ', m', .app f' a)
            | none => none
  | c, hs, ρ, m, .con1 ct a =>
      match troot? c hs ρ m (.con1 ct a) with
      | some cfg => some cfg
      | none =>
          match tstep? c hs ρ m a with
          | some (c', hs', ρ', m', a') => some (c', hs', ρ', m', .con1 ct a')
          | none => none
  | c, hs, ρ, m, .con2 ct a b =>
      match troot? c hs ρ m (.con2 ct a b) with
      | some cfg => some cfg
      | none =>
          match tstep? c hs ρ m a with
          | some (c', hs', ρ', m', a') => some (c', hs', ρ', m', .con2 ct a' b)
          | none =>
              if valueB a then
                match tstep? c hs ρ m b with
                | some (c', hs', ρ', m', b') => some (c', hs', ρ', m', .con2 ct a b')
                | none => none
              else none
  | c, hs, ρ, m, .dup y e => troot? c hs ρ m (.dup y e)
  | c, hs, ρ, m, .drop y e => troot? c hs ρ m (.drop y e)
  | c, hs, ρ, m, .matchC s ctag ys body => troot? c hs ρ m (.matchC s ctag ys body)
  | c, hs, ρ, m, .store s i v => troot? c hs ρ m (.store s i v)
  | c, hs, ρ, m, .var x => troot? c hs ρ m (.var x)
  | c, hs, ρ, m, .lam x body => troot? c hs ρ m (.lam x body)
  | c, hs, ρ, m, .con0 ctag => troot? c hs ρ m (.con0 ctag)

/-- `n` steps of the evaluator, or the configuration it is stuck at. -/
def trun : Nat → CHeap × List Ref × TEnv × Multi × Expr →
    CHeap × List Ref × TEnv × Multi × Expr
  | 0, cfg => cfg
  | n + 1, (c, hs, ρ, m, e) =>
      match tstep? c hs ρ m e with
      | none => (c, hs, ρ, m, e)
      | some (c', hs', ρ', m', e') => trun n (c', hs', ρ', m', e')

/-- The value realization the evaluator answers is a `ValRef`. -/
theorem claim?_sound : ∀ (c : CHeap) (hs : List Ref) (ρ : TEnv) (v : Expr) (c' : CHeap)
    (hs' : List Ref) (r : Ref), claim? c hs ρ v = some (c', hs', r) → ValRef c hs ρ v c' hs' r
  | c, hs, ρ, .var x, c', hs', r, h => by
      cases hlook : ρ.lookup x with
      | none => simp [claim?, hlook] at h
      | some r₀ =>
          simp only [claim?, hlook] at h
          by_cases hlive : live c r₀
          · rw [ite_eq_left hlive] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ValRef.var hlook (live_eq_true hlive)
          · rw [ite_eq_right hlive] at h
            exact absurd h (by simp)
  | c, hs, ρ, .lam x body, c', hs', r, h => by
      simp only [claim?] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ValRef.lam
  | c, hs, ρ, .con0 ctag, c', hs', r, h => by
      simp only [claim?] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ValRef.con0
  | c, hs, ρ, .con1 ctag a, c', hs', r, h => by
      cases ha : claim? c hs ρ a with
      | none => simp [claim?, ha] at h
      | some q =>
          obtain ⟨c₁, hs₁, r₁⟩ := q
          simp only [claim?, ha] at h
          by_cases hlive : live c₁ r₁
          · rw [ite_eq_left hlive] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ValRef.con1 (claim?_sound c hs ρ a c₁ hs₁ r₁ ha) (live_eq_true hlive)
          · rw [ite_eq_right hlive] at h
            exact absurd h (by simp)
  | c, hs, ρ, .con2 ctag a b, c', hs', r, h => by
      cases ha : claim? c hs ρ a with
      | none => simp [claim?, ha] at h
      | some q =>
          obtain ⟨c₁, hs₁, r₁⟩ := q
          cases hb : claim? c₁ hs₁ ρ b with
          | none => simp [claim?, ha, hb] at h
          | some q' =>
              obtain ⟨c₂, hs₂, r₂⟩ := q'
              simp only [claim?, ha, hb] at h
              by_cases hlive : live c₂ r₁ && live c₂ r₂
              · rw [ite_eq_left hlive] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact ValRef.con2 (claim?_sound c hs ρ a c₁ hs₁ r₁ ha)
                  (claim?_sound c₁ hs₁ ρ b c₂ hs₂ r₂ hb)
                  (live_eq_true (Bool.and_eq_true_iff.mp hlive).1)
                  (live_eq_true (Bool.and_eq_true_iff.mp hlive).2)
              · rw [ite_eq_right hlive] at h
                exact absurd h (by simp)
  | c, hs, ρ, .app f a, c', hs', r, h => by simp [claim?] at h
  | c, hs, ρ, .bind x e₁ e₂, c', hs', r, h => by simp [claim?] at h
  | c, hs, ρ, .matchC s ctag ys body, c', hs', r, h => by simp [claim?] at h
  | c, hs, ρ, .dup x e, c', hs', r, h => by simp [claim?] at h
  | c, hs, ρ, .drop x e, c', hs', r, h => by simp [claim?] at h
  | c, hs, ρ, .store s i v, c', hs', r, h => by simp [claim?] at h

/-- The rule the evaluator answers at a term's own root is a rule of the relation. -/
theorem troot?_sound : ∀ (c : CHeap) (hs : List Ref) (ρ : TEnv) (m : Multi) (e : Expr)
    (c' : CHeap) (hs' : List Ref) (ρ' : TEnv) (m' : Multi) (e' : Expr),
    troot? c hs ρ m e = some (c', hs', ρ', m', e') → TStep c hs ρ m e c' hs' ρ' m' e'
  | c, hs, ρ, m, .dup y body, c', hs', ρ', m', e', h => by
      cases hρ : ρ.lookup y with
      | none => simp [troot?, hρ] at h
      | some r =>
          simp only [troot?, hρ] at h
          by_cases hlive : live c r
          · rw [ite_eq_left hlive] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
            exact TStep.dup hρ (live_eq_true hlive)
          · rw [ite_eq_right hlive] at h
            exact absurd h (by simp)
  | c, hs, ρ, m, .drop y body, c', hs', ρ', m', e', h => by
      cases hρ : ρ.lookup y with
      | none => simp [troot?, hρ] at h
      | some r =>
          simp only [troot?, hρ] at h
          by_cases hsub : (y, r) ∈ m
          · rw [ite_eq_left hsub] at h
            by_cases h1 : CHeap.count c r = 1
            · rw [ite_eq_left h1] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
              exact TStep.dropFinal hρ h1 hsub
            · rw [ite_eq_right h1] at h
              by_cases h2 : 2 ≤ CHeap.count c r
              · rw [ite_eq_left h2] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                exact TStep.dropShared hρ h2 hsub
              · rw [ite_eq_right h2] at h
                exact absurd h (by simp)
          · rw [ite_eq_right hsub] at h
            exact absurd h (by simp)
  | c, hs, ρ, m, .bind x v e₂, c', hs', ρ', m', e', h => by
      cases v with
      | var z =>
          simp only [troot?] at h
          cases hρ : ρ.lookup z with
          | none => simp [hρ] at h
          | some r =>
              simp only [hρ] at h
              by_cases hchk : (z, r) ∈ m && nameOnly m x r
              · rw [ite_eq_left hchk] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                exact TStep.bindVar hρ (of_decide_eq_true (Bool.and_eq_true_iff.mp hchk).1)
                  (Bool.and_eq_true_iff.mp hchk).2
              · rw [ite_eq_right hchk] at h
                exact absurd h (by simp)
      | lam x' body =>
          simp only [troot?] at h
          by_cases hchk : freeName m x
          · rw [ite_eq_left hchk] at h
            have hv : claim? c hs ρ (.lam x' body)
                = some ((allocWith c hs []).1, (allocWith c hs []).2, fresh c []) := rfl
            rw [hv] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
            exact TStep.bindVal (claim?_sound c hs ρ (.lam x' body) _ _ _ hv)
              (by intro z hh; cases hh) hchk
          · rw [ite_eq_right hchk] at h
            exact absurd h (by simp)
      | con0 ctag =>
          simp only [troot?] at h
          by_cases hchk : freeName m x
          · rw [ite_eq_left hchk] at h
            have hv : claim? c hs ρ (.con0 ctag)
                = some ((allocWith c hs []).1, (allocWith c hs []).2, fresh c []) := rfl
            rw [hv] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
            exact TStep.bindVal (claim?_sound c hs ρ (.con0 ctag) _ _ _ hv)
              (by intro z hh; cases hh) hchk
          · rw [ite_eq_right hchk] at h
            exact absurd h (by simp)
      | con1 ctag a =>
          simp only [troot?] at h
          by_cases hchk : freeName m x
          · rw [ite_eq_left hchk] at h
            cases hv : claim? c hs ρ (.con1 ctag a) with
            | none => simp [hv] at h
            | some q =>
                obtain ⟨c₁, hs₁, r₁⟩ := q
                simp only [hv] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                exact TStep.bindVal (claim?_sound c hs ρ (.con1 ctag a) c₁ hs₁ r₁ hv)
                  (by intro z hh; cases hh) hchk
          · rw [ite_eq_right hchk] at h
            exact absurd h (by simp)
      | con2 ctag a b =>
          simp only [troot?] at h
          by_cases hchk : freeName m x
          · rw [ite_eq_left hchk] at h
            cases hv : claim? c hs ρ (.con2 ctag a b) with
            | none => simp [hv] at h
            | some q =>
                obtain ⟨c₁, hs₁, r₁⟩ := q
                simp only [hv] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                exact TStep.bindVal (claim?_sound c hs ρ (.con2 ctag a b) c₁ hs₁ r₁ hv)
                  (by intro z hh; cases hh) hchk
          · rw [ite_eq_right hchk] at h
            exact absurd h (by simp)
      | app f a => simp [troot?, claim?] at h
      | bind x' e₁ e₂ => simp [troot?, claim?] at h
      | matchC s ctag ys body => simp [troot?, claim?] at h
      | dup z e => simp [troot?, claim?] at h
      | drop z e => simp [troot?, claim?] at h
      | store s i w => simp [troot?, claim?] at h
  | c, hs, ρ, m, .app f a, c', hs', ρ', m', e', h => by
      cases f with
      | lam x body =>
          cases a with
          | var z =>
              simp only [troot?] at h
              cases hρ : ρ.lookup z with
              | none => simp [hρ] at h
              | some r =>
                  simp only [hρ] at h
                  by_cases hchk : (z, r) ∈ m && nameOnly m x r
                  · rw [ite_eq_left hchk] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                    exact TStep.appVar hρ (of_decide_eq_true (Bool.and_eq_true_iff.mp hchk).1)
                      (Bool.and_eq_true_iff.mp hchk).2
                  · rw [ite_eq_right hchk] at h
                    exact absurd h (by simp)
          | lam x' body' =>
              simp only [troot?] at h
              by_cases hchk : freeName m x
              · rw [ite_eq_left hchk] at h
                have hv : claim? c hs ρ (.lam x' body')
                    = some ((allocWith c hs []).1, (allocWith c hs []).2, fresh c []) := rfl
                rw [hv] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                exact TStep.appVal (claim?_sound c hs ρ (.lam x' body') _ _ _ hv)
                  (by intro z hh; cases hh) hchk
              · rw [ite_eq_right hchk] at h
                exact absurd h (by simp)
          | con0 ctag =>
              simp only [troot?] at h
              by_cases hchk : freeName m x
              · rw [ite_eq_left hchk] at h
                have hv : claim? c hs ρ (.con0 ctag)
                    = some ((allocWith c hs []).1, (allocWith c hs []).2, fresh c []) := rfl
                rw [hv] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                exact TStep.appVal (claim?_sound c hs ρ (.con0 ctag) _ _ _ hv)
                  (by intro z hh; cases hh) hchk
              · rw [ite_eq_right hchk] at h
                exact absurd h (by simp)
          | con1 ctag a =>
              simp only [troot?] at h
              by_cases hchk : freeName m x
              · rw [ite_eq_left hchk] at h
                cases hv : claim? c hs ρ (.con1 ctag a) with
                | none => simp [hv] at h
                | some q =>
                    obtain ⟨c₁, hs₁, r₁⟩ := q
                    simp only [hv] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                    exact TStep.appVal (claim?_sound c hs ρ (.con1 ctag a) c₁ hs₁ r₁ hv)
                      (by intro z hh; cases hh) hchk
              · rw [ite_eq_right hchk] at h
                exact absurd h (by simp)
          | con2 ctag a b =>
              simp only [troot?] at h
              by_cases hchk : freeName m x
              · rw [ite_eq_left hchk] at h
                cases hv : claim? c hs ρ (.con2 ctag a b) with
                | none => simp [hv] at h
                | some q =>
                    obtain ⟨c₁, hs₁, r₁⟩ := q
                    simp only [hv] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                    exact TStep.appVal (claim?_sound c hs ρ (.con2 ctag a b) c₁ hs₁ r₁ hv)
                      (by intro z hh; cases hh) hchk
              · rw [ite_eq_right hchk] at h
                exact absurd h (by simp)
          | app g b => simp [troot?, claim?] at h
          | bind z e₁ e₂ => simp [troot?, claim?] at h
          | matchC s ctag ys body => simp [troot?, claim?] at h
          | dup z e => simp [troot?, claim?] at h
          | drop z e => simp [troot?, claim?] at h
          | store s i w => simp [troot?, claim?] at h
      | var x => simp [troot?] at h
      | app g b => simp [troot?] at h
      | bind z e₁ e₂ => simp [troot?] at h
      | matchC s ctag ys body => simp [troot?] at h
      | dup z e => simp [troot?] at h
      | drop z e => simp [troot?] at h
      | con0 ctag => simp [troot?] at h
      | con1 ctag g => simp [troot?] at h
      | con2 ctag g g' => simp [troot?] at h
      | store s i w => simp [troot?] at h
  | c, hs, ρ, m, .matchC s ctag ys body, c', hs', ρ', m', e', h => by
      cases s with
      | var z =>
          cases hρ : ρ.lookup z with
          | none => simp [troot?, hρ] at h
          | some r =>
              simp only [troot?, hρ] at h
              by_cases hchk : ys.length = (CHeap.slotsAt c r).length && freeOf m ys
              · rw [ite_eq_left hchk] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                exact TStep.matchC hρ (of_decide_eq_true (Bool.and_eq_true_iff.mp hchk).1)
                  (freeOf_eq_true (Bool.and_eq_true_iff.mp hchk).2)
              · rw [ite_eq_right hchk] at h
                exact absurd h (by simp)
      | lam x body => simp [troot?] at h
      | app f a => simp [troot?] at h
      | bind x e₁ e₂ => simp [troot?] at h
      | matchC s ctag ys body => simp [troot?] at h
      | dup x e => simp [troot?] at h
      | drop x e => simp [troot?] at h
      | con0 ctag => simp [troot?] at h
      | con1 ctag a => simp [troot?] at h
      | con2 ctag a b => simp [troot?] at h
      | store s i v => simp [troot?] at h
  | c, hs, ρ, m, .store s i v, c', hs', ρ', m', e', h => by
      cases s with
      | var y =>
          cases hρ : ρ.lookup y with
          | none => simp [troot?, hρ] at h
          | some r =>
              cases hv : claim? c hs ρ v with
              | none => simp [troot?, hρ, hv] at h
              | some q =>
                  obtain ⟨c₁, hs₁, wv⟩ := q
                  simp only [troot?, hρ, hv] at h
                  by_cases hchk : i < (CHeap.slotsAt c₁ r).length
                    && writeCheck c₁ r (storeSlots c₁ r i wv)
                  · rw [ite_eq_left hchk] at h
                    have hlen : i < (CHeap.slotsAt c₁ r).length :=
                      of_decide_eq_true (Bool.and_eq_true_iff.mp hchk).1
                    have hw : writeCheck c₁ r (storeSlots c₁ r i wv) = true :=
                      (Bool.and_eq_true_iff.mp hchk).2
                    by_cases h1 : CHeap.count c₁ r = 1
                    · rw [ite_eq_left h1] at h
                      by_cases hsub : (y, r) ∈ m
                      · rw [ite_eq_left hsub] at h
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                        exact TStep.storeExclusive hρ (claim?_sound c hs ρ v c₁ hs₁ wv hv) hlen
                          hw h1 hsub
                      · rw [ite_eq_right hsub] at h
                        exact absurd h (by simp)
                    · rw [ite_eq_right h1] at h
                      by_cases hchk' : (y, r) ∈ m && nameGone m y r
                      · rw [ite_eq_left hchk'] at h
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                        exact TStep.storeShared hρ (claim?_sound c hs ρ v c₁ hs₁ wv hv) hlen hw
                          (of_decide_eq_true (Bool.and_eq_true_iff.mp hchk').1)
                          (Bool.and_eq_true_iff.mp hchk').2 h1
                      · rw [ite_eq_right hchk'] at h
                        exact absurd h (by simp)
                  · rw [ite_eq_right hchk] at h
                    exact absurd h (by simp)
      | lam x body => simp [troot?] at h
      | app f a => simp [troot?] at h
      | bind x e₁ e₂ => simp [troot?] at h
      | matchC s ctag ys body => simp [troot?] at h
      | dup x e => simp [troot?] at h
      | drop x e => simp [troot?] at h
      | con0 ctag => simp [troot?] at h
      | con1 ctag a => simp [troot?] at h
      | con2 ctag a b => simp [troot?] at h
      | store s i v => simp [troot?] at h
  | c, hs, ρ, m, .var x, c', hs', ρ', m', e', h => by simp [troot?] at h
  | c, hs, ρ, m, .lam x body, c', hs', ρ', m', e', h => by simp [troot?] at h
  | c, hs, ρ, m, .con0 ctag, c', hs', ρ', m', e', h => by simp [troot?] at h
  | c, hs, ρ, m, .con1 ctag a, c', hs', ρ', m', e', h => by simp [troot?] at h
  | c, hs, ρ, m, .con2 ctag a b, c', hs', ρ', m', e', h => by simp [troot?] at h

/-- The step the evaluator answers is a step of the relation: the rule the root
takes where it takes one, and otherwise the position the search reaches. -/
theorem tstep?_sound : ∀ (c : CHeap) (hs : List Ref) (ρ : TEnv) (m : Multi) (e : Expr)
    (c' : CHeap) (hs' : List Ref) (ρ' : TEnv) (m' : Multi) (e' : Expr),
    tstep? c hs ρ m e = some (c', hs', ρ', m', e') → TStep c hs ρ m e c' hs' ρ' m' e'
  | c, hs, ρ, m, .bind x e₁ e₂, c', hs', ρ', m', e', h => by
      cases ht : troot? c hs ρ m (.bind x e₁ e₂) with
      | some q =>
          obtain ⟨c₁, hs₁, ρ₁, m₁, e₁'⟩ := q
          simp only [tstep?, ht, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
          exact troot?_sound c hs ρ m (.bind x e₁ e₂) c₁ hs₁ ρ₁ m₁ e₁' ht
      | none =>
          have hred : tstep? c hs ρ m (.bind x e₁ e₂)
              = (match tstep? c hs ρ m e₁ with
                 | some (c₁, hs₁, ρ₁, m₁, e₁') => some (c₁, hs₁, ρ₁, m₁, .bind x e₁' e₂)
                 | none => none) := by
            simp only [tstep?, ht]
          rw [hred] at h
          cases hsub : tstep? c hs ρ m e₁ with
          | none => simp [hsub] at h
          | some q =>
              obtain ⟨c₂, hs₂, ρ₂, m₂, e₁'⟩ := q
              simp only [hsub, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
              exact TStep.bindRhs (tstep?_sound c hs ρ m e₁ c₂ hs₂ ρ₂ m₂ e₁' hsub)
  | c, hs, ρ, m, .app f a, c', hs', ρ', m', e', h => by
      cases ht : troot? c hs ρ m (.app f a) with
      | some q =>
          obtain ⟨c₁, hs₁, ρ₁, m₁, e₁'⟩ := q
          simp only [tstep?, ht, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
          exact troot?_sound c hs ρ m (.app f a) c₁ hs₁ ρ₁ m₁ e₁' ht
      | none =>
          have hred : tstep? c hs ρ m (.app f a)
              = (if valueB f then
                   (match tstep? c hs ρ m a with
                    | some (c₁, hs₁, ρ₁, m₁, a') => some (c₁, hs₁, ρ₁, m₁, .app f a')
                    | none => none)
                 else
                   (match tstep? c hs ρ m f with
                    | some (c₁, hs₁, ρ₁, m₁, f') => some (c₁, hs₁, ρ₁, m₁, .app f' a)
                    | none => none)) := by
            simp only [tstep?, ht]
          rw [hred] at h
          by_cases hval : valueB f
          · rw [ite_eq_left hval] at h
            cases hsub : tstep? c hs ρ m a with
            | none => simp [hsub] at h
            | some q =>
                obtain ⟨c₂, hs₂, ρ₂, m₂, a'⟩ := q
                simp only [hsub, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                exact TStep.appArg ((valueB_iff f).mp hval)
                  (tstep?_sound c hs ρ m a c₂ hs₂ ρ₂ m₂ a' hsub)
          · rw [ite_eq_right hval] at h
            cases hsub : tstep? c hs ρ m f with
            | none => simp [hsub] at h
            | some q =>
                obtain ⟨c₂, hs₂, ρ₂, m₂, f'⟩ := q
                simp only [hsub, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                exact TStep.appFun (tstep?_sound c hs ρ m f c₂ hs₂ ρ₂ m₂ f' hsub)
  | c, hs, ρ, m, .con1 ct a, c', hs', ρ', m', e', h => by
      cases ht : troot? c hs ρ m (.con1 ct a) with
      | some q =>
          obtain ⟨c₁, hs₁, ρ₁, m₁, e₁'⟩ := q
          simp only [tstep?, ht, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
          exact troot?_sound c hs ρ m (.con1 ct a) c₁ hs₁ ρ₁ m₁ e₁' ht
      | none =>
          have hred : tstep? c hs ρ m (.con1 ct a)
              = (match tstep? c hs ρ m a with
                 | some (c₁, hs₁, ρ₁, m₁, a') => some (c₁, hs₁, ρ₁, m₁, .con1 ct a')
                 | none => none) := by
            simp only [tstep?, ht]
          rw [hred] at h
          cases hsub : tstep? c hs ρ m a with
          | none => simp [hsub] at h
          | some q =>
              obtain ⟨c₂, hs₂, ρ₂, m₂, a'⟩ := q
              simp only [hsub, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
              exact TStep.con1Field (tstep?_sound c hs ρ m a c₂ hs₂ ρ₂ m₂ a' hsub)
  | c, hs, ρ, m, .con2 ct a b, c', hs', ρ', m', e', h => by
      cases ht : troot? c hs ρ m (.con2 ct a b) with
      | some q =>
          obtain ⟨c₁, hs₁, ρ₁, m₁, e₁'⟩ := q
          simp only [tstep?, ht, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
          exact troot?_sound c hs ρ m (.con2 ct a b) c₁ hs₁ ρ₁ m₁ e₁' ht
      | none =>
          have hred : tstep? c hs ρ m (.con2 ct a b)
              = (match tstep? c hs ρ m a with
                 | some (c₁, hs₁, ρ₁, m₁, a') => some (c₁, hs₁, ρ₁, m₁, .con2 ct a' b)
                 | none =>
                     if valueB a then
                       (match tstep? c hs ρ m b with
                        | some (c₁, hs₁, ρ₁, m₁, b') => some (c₁, hs₁, ρ₁, m₁, .con2 ct a b')
                        | none => none)
                     else none) := by
            simp only [tstep?, ht]
          rw [hred] at h
          cases hsub : tstep? c hs ρ m a with
          | some q =>
              obtain ⟨c₂, hs₂, ρ₂, m₂, a'⟩ := q
              simp only [hsub, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
              exact TStep.con2FieldL (tstep?_sound c hs ρ m a c₂ hs₂ ρ₂ m₂ a' hsub)
          | none =>
              simp only [hsub] at h
              by_cases hval : valueB a
              · rw [ite_eq_left hval] at h
                cases hsub' : tstep? c hs ρ m b with
                | none => simp [hsub'] at h
                | some q =>
                    obtain ⟨c₂, hs₂, ρ₂, m₂, b'⟩ := q
                    simp only [hsub', Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                    exact TStep.con2FieldR ((valueB_iff a).mp hval)
                      (tstep?_sound c hs ρ m b c₂ hs₂ ρ₂ m₂ b' hsub')
              · rw [ite_eq_right hval] at h
                exact absurd h (by simp)
  | c, hs, ρ, m, .dup y e, c', hs', ρ', m', e', h => by
      simp only [tstep?] at h
      exact troot?_sound c hs ρ m (.dup y e) c' hs' ρ' m' e' h
  | c, hs, ρ, m, .drop y e, c', hs', ρ', m', e', h => by
      simp only [tstep?] at h
      exact troot?_sound c hs ρ m (.drop y e) c' hs' ρ' m' e' h
  | c, hs, ρ, m, .matchC s ctag ys body, c', hs', ρ', m', e', h => by
      simp only [tstep?] at h
      exact troot?_sound c hs ρ m (.matchC s ctag ys body) c' hs' ρ' m' e' h
  | c, hs, ρ, m, .store s i v, c', hs', ρ', m', e', h => by
      simp only [tstep?] at h
      exact troot?_sound c hs ρ m (.store s i v) c' hs' ρ' m' e' h
  | c, hs, ρ, m, .var x, c', hs', ρ', m', e', h => by
      simp only [tstep?] at h
      exact troot?_sound c hs ρ m (.var x) c' hs' ρ' m' e' h
  | c, hs, ρ, m, .lam x body, c', hs', ρ', m', e', h => by
      simp only [tstep?] at h
      exact troot?_sound c hs ρ m (.lam x body) c' hs' ρ' m' e' h
  | c, hs, ρ, m, .con0 ctag, c', hs', ρ', m', e', h => by
      simp only [tstep?] at h
      exact troot?_sound c hs ρ m (.con0 ctag) c' hs' ρ' m' e' h

/-! ## Runs -/

/-- The reflexive-transitive closure of the target step relation: a run of a term
on the counted heap. -/
inductive TStepStar :
    CHeap → List Ref → TEnv → Multi → Expr → CHeap → List Ref → TEnv → Multi → Expr → Prop where
  /-- A term with no step is reached from itself. -/
  | refl {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {e : Expr} :
      TStepStar c hs ρ m e c hs ρ m e
  /-- A step and the run after it. -/
  | step {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {e : Expr} {c' : CHeap}
      {hs' : List Ref} {ρ' : TEnv} {m' : Multi} {e' : Expr} {c'' : CHeap} {hs'' : List Ref}
      {ρ'' : TEnv} {m'' : Multi} {e'' : Expr} (h : TStep c hs ρ m e c' hs' ρ' m' e')
      (hr : TStepStar c' hs' ρ' m' e' c'' hs'' ρ'' m'' e'') :
      TStepStar c hs ρ m e c'' hs'' ρ'' m'' e''

/-- Every configuration the evaluator reaches is reached by the step relation, so a
guarded run is a fact about the reduction. -/
theorem trun_stepStar (n : Nat) : ∀ (c : CHeap) (hs : List Ref) (ρ : TEnv) (m : Multi) (e : Expr),
    TStepStar c hs ρ m e (trun n (c, hs, ρ, m, e)).1 (trun n (c, hs, ρ, m, e)).2.1
      (trun n (c, hs, ρ, m, e)).2.2.1 (trun n (c, hs, ρ, m, e)).2.2.2.1
      (trun n (c, hs, ρ, m, e)).2.2.2.2 := by
  induction n with
  | zero => intro c hs ρ m e; exact TStepStar.refl
  | succ n ih =>
      intro c hs ρ m e
      cases hstep : tstep? c hs ρ m e with
      | none =>
          have hrun : trun (n + 1) (c, hs, ρ, m, e) = (c, hs, ρ, m, e) := by
            simp only [trun, hstep]
          rw [hrun]
          exact TStepStar.refl
      | some cfg =>
          obtain ⟨c', hs', ρ', m', e'⟩ := cfg
          have hrun : trun (n + 1) (c, hs, ρ, m, e) = trun n (c', hs', ρ', m', e') := by
            simp only [trun, hstep]
          rw [hrun]
          exact TStepStar.step (tstep?_sound c hs ρ m e c' hs' ρ' m' e' hstep) (ih c' hs' ρ' m' e')

end Scidonia.RC
