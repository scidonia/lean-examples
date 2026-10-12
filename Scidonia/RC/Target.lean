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

**Configurations, and the A-normal form.** A configuration is a heap, the handles
held outside the term, a runtime environment binding variables to references, the
term's own multiplicities and the term. The rules are one per instruction and there
are no congruence rules: λ¹ is an A-normal calculus and the lowering of
`Scidonia.RC.Lower` emits terms in that shape, so every subject and every argument
is already a value. The subjects a rule reads through the environment are
variables; a node construction in a value position is realised by `ValRef`, which
allocates its cell; and a write's subject is the variable the derivation bound,
which is what makes the store's branch a statement about that variable's
reference.

The multiplicities are part of the configuration rather than read off the term,
because an instruction moves them against the term's own syntactic occurrences: a
`dup x; e` step takes the term's multiplicity of `x` from `n` to `n + 1` — the
instruction supplies the occurrence `e` uses and the term `dup x; e` writes — and a
`drop x; e` step takes it from `n + 1` to `n`. The counts the heap keeps are
`Counted`'s, stated at the run's handles together with the term's own references;
`Scidonia.RC.Ownership` is that statement and its preservation.

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

/-- The multiplicity a `drop` step leaves: one occurrence of the released
reference leaves the term's own — the one the instruction consumes. -/
def Multi.dropFirst : Multi → Ref → Multi
  | [], _ => []
  | (x, r') :: t, r => if r' = r then t else (x, r') :: Multi.dropFirst t r

/-- The reference a `drop` consumes is the one the count falls at by one. -/
theorem expand_dropFirst_count_self (m : Multi) (r : Ref) :
    (expand (Multi.dropFirst m r)).count r = (expand m).count r - 1 := by
  induction m with
  | nil => simp [Multi.dropFirst]
  | cons p t ih =>
      obtain ⟨x, r'⟩ := p
      by_cases h : r' = r
      · have hdrop : Multi.dropFirst ((x, r') :: t) r = t := by simp [Multi.dropFirst, h]
        rw [hdrop, expand_cons, h, List.count_cons_self]
        omega
      · have hdrop : Multi.dropFirst ((x, r') :: t) r = (x, r') :: Multi.dropFirst t r := by
          simp [Multi.dropFirst, h]
        rw [hdrop, expand_cons, expand_cons, List.count_cons_of_ne h, List.count_cons_of_ne h]
        exact ih

/-- A `drop` of another reference leaves this one's count alone. -/
theorem expand_dropFirst_count_of_ne (m : Multi) {r r' : Ref} (h : r' ≠ r) :
    (expand (Multi.dropFirst m r')).count r = (expand m).count r := by
  induction m with
  | nil => rfl
  | cons p t ih =>
      obtain ⟨x, s⟩ := p
      by_cases hs : s = r'
      · have hdrop : Multi.dropFirst ((x, s) :: t) r' = t := by simp [Multi.dropFirst, hs]
        have hsr : s ≠ r := fun hh => h (hs.symm.trans hh)
        rw [hdrop, expand_cons, List.count_cons_of_ne hsr]
      · have hdrop : Multi.dropFirst ((x, s) :: t) r' = (x, s) :: Multi.dropFirst t r' := by
          simp [Multi.dropFirst, hs]
        rw [hdrop, expand_cons, expand_cons]
        by_cases hsr : s = r
        · rw [hsr, List.count_cons_self, List.count_cons_self, ih]
        · rw [List.count_cons_of_ne hsr, List.count_cons_of_ne hsr]
          exact ih

/-- A `drop` leaves only pairs of the multiplicity it was handed. -/
theorem mem_dropFirst {p : Var × Ref} {m : Multi} {r : Ref}
    (h : p ∈ Multi.dropFirst m r) : p ∈ m := by
  induction m with
  | nil => simp [Multi.dropFirst] at h
  | cons q t ih =>
      obtain ⟨x, s⟩ := q
      by_cases hs : s = r
      · have hdrop : Multi.dropFirst ((x, s) :: t) r = t := by simp [Multi.dropFirst, hs]
        rw [hdrop] at h
        exact List.mem_cons_of_mem _ h
      · have hdrop : Multi.dropFirst ((x, s) :: t) r = (x, s) :: Multi.dropFirst t r := by
          simp [Multi.dropFirst, hs]
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

/-- Whether a value is one the realization allocates a cell for: every value but a
variable, whose reference is the one the environment already binds. -/
def allocB : Expr → Bool
  | .var _ => false
  | _ => true

/-- A value the realization allocates for is not a variable. -/
theorem allocB_eq_true {v : Expr} (h : allocB v = true) : ∀ z, v ≠ .var z := by
  intro z hh
  rw [hh] at h
  exact Bool.noConfusion h

/-- A value the realization does not allocate for is a variable. -/
theorem exists_var_of_allocB_eq_false {v : Expr} (h : allocB v = false) : ∃ z, v = .var z := by
  cases v with
  | var z => exact ⟨z, rfl⟩
  | lam x body => simp [allocB] at h
  | app f a => simp [allocB] at h
  | bind x e₁ e₂ => simp [allocB] at h
  | matchC s ctag ys body => simp [allocB] at h
  | dup x e => simp [allocB] at h
  | drop x e => simp [allocB] at h
  | con0 ctag => simp [allocB] at h
  | con1 ctag a => simp [allocB] at h
  | con2 ctag a b => simp [allocB] at h
  | store s i v => simp [allocB] at h

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

One rule per instruction of the A-normal target. Each rule's contractum carries the
multiplicity the instruction leaves, and the rules that read the term's own
occurrences — `drop` and a shared store — require that the term holds the
occurrence they consume. -/

/-- A step of the target runtime: the heap, the handles held outside the term, the
environment, the term's multiplicities and the term, and what the instruction
leaves of each.

* `dup y; e` performs the runtime's increment at the cell `y` names and adds the
  occurrence it supplies to the term's own.
* `drop y; e` performs the runtime's non-final decrement at a cell of count two or
  more, and the runtime's final release at a cell of count one, and removes the
  occurrence the term held from its own list. The occurrence is what the rule
  requires: a `drop` of a reference the term does not hold is not a step, which is
  the shape the lowering's `surplus` emits.
* `val x = v; e₂` binds `x` to the value's reference. At a variable the heap and
  the run's handles are what they were — the variable's own occurrence becomes the
  binder's, which is why the rule requires that occurrence to be one the term
  holds — and at an allocated value the realization allocates the cell and hands
  out its handle, which the binder takes up in place of the occurrence it adds.
* `(λx. body) v` resumes the body with `x` bound to the argument's reference, in
  the same two shapes.
* `match (var z) { c ȳ → body }` binds the arm's binders to the slots of the cell
  `z` names, in order, and resumes the body; the cell's tag is not read, and the
  rule requires the binders to shadow none of the names the term holds.
* `store (var y) i v` is `RCHeap.update` at the cell `y` names, with the cell's
  slots `i` set to the value's reference, at the handles the run holds plus the
  term's own occurrences. At a count of one it is destructive and leaves the
  multiplicity and the handles alone — the write's result names the cell it wrote.
  Otherwise it copies: the binder names the fresh location, one occurrence of the
  old reference leaves the term's own, and the run's handles stay as they were. -/
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
      (hm : 0 < (expand m).count r) :
      TStep c hs ρ m (.drop y e) (decRef c hs r).1 hs ρ (Multi.dropFirst m r) e
  /-- The runtime's final release at a cell of count one, and the occurrence the
  term held. -/
  | dropFinal {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {r : Ref}
      {e : Expr} (hρ : ρ.lookup y = some r) (h1 : CHeap.count c r = 1)
      (hm : 0 < (expand m).count r) :
      TStep c hs ρ m (.drop y e) (release c hs r).1 hs ρ (Multi.dropFirst m r) e
  /-- A binding whose bound term is a variable: the heap and the run's handles are
  what they were, and the variable's own occurrence becomes the binder's. The rule
  requires that occurrence to be one the term holds, which is the reading of a use
  of a variable. -/
  | bindVar {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x z : Var} {e₂ : Expr}
      {r : Ref} (hρ : ρ.lookup z = some r) (hm : 0 < (expand m).count r) :
      TStep c hs ρ m (.bind x (.var z) e₂) c hs (TEnv.set ρ x r)
        (Multi.insert (Multi.dropFirst m r) x r) e₂
  /-- A binding whose bound term is an allocated value: the value is realised and
  the binder takes up the reference the realization handed out, so the allocated
  cell is named by the binder's occurrence where it was named by the realization's
  handle. -/
  | bindVal {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x : Var} {v e₂ : Expr}
      {c' : CHeap} {hs' : List Ref} {r : Ref} (hv : ValRef c hs ρ v c' hs' r)
      (halloc : ∀ z, v ≠ .var z) :
      TStep c hs ρ m (.bind x v e₂) c' (dropHandle hs' r) (TEnv.set ρ x r)
        (Multi.insert m x r) e₂
  /-- An application of an abstraction whose argument is a variable: the body
  resumes with the parameter bound to the variable's occurrence. -/
  | appVar {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x z : Var} {body : Expr}
      {r : Ref} (hρ : ρ.lookup z = some r) (hm : 0 < (expand m).count r) :
      TStep c hs ρ m (.app (.lam x body) (.var z)) c hs (TEnv.set ρ x r)
        (Multi.insert (Multi.dropFirst m r) x r) body
  /-- An application of an abstraction whose argument is an allocated value. -/
  | appVal {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {x : Var} {body v : Expr}
      {c' : CHeap} {hs' : List Ref} {r : Ref} (hv : ValRef c hs ρ v c' hs' r)
      (halloc : ∀ z, v ≠ .var z) :
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
  the cell the subject names, with the multiplicity and the handles left alone. -/
  | storeExclusive {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {i : Nat}
      {v : Expr} {c₁ : CHeap} {hs₁ : List Ref} {wv r : Ref} (hρ : ρ.lookup y = some r)
      (hv : ValRef c hs ρ v c₁ hs₁ wv) (hi : i < (CHeap.slotsAt c₁ r).length)
      (hchk : writeCheck c₁ r (storeSlots c₁ r i wv) = true) (h1 : CHeap.count c₁ r = 1) :
      TStep c hs ρ m (.store (.var y) i v)
        (update c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv)).1 hs₁ ρ m (.var y)
  /-- A store at a cell of count other than one: the copying branch of
  `RCHeap.update`, which lands the written slots at a fresh location, leaves the old
  cell its slots and one reference fewer, and rebinds the subject to the fresh
  location at one occurrence of the old reference fewer. -/
  | storeShared {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {i : Nat}
      {v : Expr} {c₁ : CHeap} {hs₁ : List Ref} {wv r : Ref} (hρ : ρ.lookup y = some r)
      (hv : ValRef c hs ρ v c₁ hs₁ wv) (hi : i < (CHeap.slotsAt c₁ r).length)
      (hchk : writeCheck c₁ r (storeSlots c₁ r i wv) = true)
      (hm : 0 < (expand m).count r) (h2 : CHeap.count c₁ r ≠ 1) :
      TStep c hs ρ m (.store (.var y) i v)
        (update c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv)).1 hs₁
        (TEnv.set ρ y (fresh c₁ (storeSlots c₁ r i wv)))
        (Multi.insert (Multi.dropFirst m r) y (fresh c₁ (storeSlots c₁ r i wv))) (.var y)

/-! ## The evaluator

The same instructions as a function: one step, and the fuel-indexed iteration of
it. `claim?` realises a value's reference, and `tstep?` performs one instruction,
answering `none` exactly where the relation has no step. -/

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

/-- One instruction, or `none` where the relation has no step. -/
def tstep? :
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
          if 0 < (expand m).count r then
            if CHeap.count c r = 1 then
              some ((release c hs r).1, hs, ρ, Multi.dropFirst m r, e)
            else if 2 ≤ CHeap.count c r then
              some ((decRef c hs r).1, hs, ρ, Multi.dropFirst m r, e)
            else none
          else none
  | c, hs, ρ, m, .bind x v e₂ =>
      match claim? c hs ρ v with
      | none => none
      | some (c₁, hs₁, r) =>
          if allocB v then
            some (c₁, dropHandle hs₁ r, TEnv.set ρ x r, Multi.insert m x r, e₂)
          else if 0 < (expand m).count r then
            some (c₁, hs₁, TEnv.set ρ x r, Multi.insert (Multi.dropFirst m r) x r, e₂)
          else none
  | c, hs, ρ, m, .app (.lam x body) a =>
      match claim? c hs ρ a with
      | none => none
      | some (c₁, hs₁, r) =>
          if allocB a then
            some (c₁, dropHandle hs₁ r, TEnv.set ρ x r, Multi.insert m x r, body)
          else if 0 < (expand m).count r then
            some (c₁, hs₁, TEnv.set ρ x r, Multi.insert (Multi.dropFirst m r) x r, body)
          else none
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
                      some ((update c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv)).1, hs₁, ρ, m, .var y)
                    else if 0 < (expand m).count r then
                      some ((update c₁ (hs₁ ++ expand m) r (storeSlots c₁ r i wv)).1, hs₁,
                        TEnv.set ρ y (fresh c₁ (storeSlots c₁ r i wv)),
                        Multi.insert (Multi.dropFirst m r) y (fresh c₁ (storeSlots c₁ r i wv)), .var y)
                    else none
                  else none
      | _ => none
  | _, _, _, _, _ => none

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

/-- The step the evaluator answers is a step of the relation. -/
theorem tstep?_sound : ∀ (c : CHeap) (hs : List Ref) (ρ : TEnv) (m : Multi) (e : Expr)
    (c' : CHeap) (hs' : List Ref) (ρ' : TEnv) (m' : Multi) (e' : Expr),
    tstep? c hs ρ m e = some (c', hs', ρ', m', e') → TStep c hs ρ m e c' hs' ρ' m' e'
  | c, hs, ρ, m, .dup y body, c', hs', ρ', m', e', h => by
      cases hρ : ρ.lookup y with
      | none => simp [tstep?, hρ] at h
      | some r =>
          simp only [tstep?, hρ] at h
          by_cases hlive : live c r
          · rw [ite_eq_left hlive] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
            exact TStep.dup hρ (live_eq_true hlive)
          · rw [ite_eq_right hlive] at h
            exact absurd h (by simp)
  | c, hs, ρ, m, .drop y body, c', hs', ρ', m', e', h => by
      cases hρ : ρ.lookup y with
      | none => simp [tstep?, hρ] at h
      | some r =>
          simp only [tstep?, hρ] at h
          by_cases hm : 0 < (expand m).count r
          · rw [ite_eq_left hm] at h
            by_cases h1 : CHeap.count c r = 1
            · rw [ite_eq_left h1] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
              exact TStep.dropFinal hρ h1 hm
            · rw [ite_eq_right h1] at h
              by_cases h2 : 2 ≤ CHeap.count c r
              · rw [ite_eq_left h2] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                exact TStep.dropShared hρ h2 hm
              · rw [ite_eq_right h2] at h
                exact absurd h (by simp)
          · rw [ite_eq_right hm] at h
            exact absurd h (by simp)
  | c, hs, ρ, m, .bind x v e₂, c', hs', ρ', m', e', h => by
      cases hv : claim? c hs ρ v with
      | none => simp [tstep?, hv] at h
      | some q =>
          obtain ⟨c₁, hs₁, r₁⟩ := q
          simp only [tstep?, hv] at h
          have hsound : ValRef c hs ρ v c₁ hs₁ r₁ := claim?_sound c hs ρ v c₁ hs₁ r₁ hv
          by_cases halloc : allocB v
          · rw [ite_eq_left halloc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
            exact TStep.bindVal hsound (allocB_eq_true halloc)
          · rw [ite_eq_right halloc] at h
            have hfalse : allocB v = false := by
              cases hv2 : allocB v with
              | false => rfl
              | true => exact absurd hv2 halloc
            by_cases hm : 0 < (expand m).count r₁
            · rw [ite_eq_left hm] at h
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
              obtain ⟨z, rfl⟩ := exists_var_of_allocB_eq_false hfalse
              cases hsound with
              | var hρ hlive => exact TStep.bindVar hρ hm
            · rw [ite_eq_right hm] at h
              exact absurd h (by simp)
  | c, hs, ρ, m, .app f a, c', hs', ρ', m', e', h => by
      cases f with
      | lam x body =>
          cases hv : claim? c hs ρ a with
          | none => simp [tstep?, hv] at h
          | some q =>
              obtain ⟨c₁, hs₁, r₁⟩ := q
              simp only [tstep?, hv] at h
              have hsound : ValRef c hs ρ a c₁ hs₁ r₁ := claim?_sound c hs ρ a c₁ hs₁ r₁ hv
              by_cases halloc : allocB a
              · rw [ite_eq_left halloc] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                exact TStep.appVal hsound (allocB_eq_true halloc)
              · rw [ite_eq_right halloc] at h
                have hfalse : allocB a = false := by
                  cases hv2 : allocB a with
                  | false => rfl
                  | true => exact absurd hv2 halloc
                by_cases hm : 0 < (expand m).count r₁
                · rw [ite_eq_left hm] at h
                  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                  obtain ⟨z, rfl⟩ := exists_var_of_allocB_eq_false hfalse
                  cases hsound with
                  | var hρ hlive => exact TStep.appVar hρ hm
                · rw [ite_eq_right hm] at h
                  exact absurd h (by simp)
      | var x => simp [tstep?] at h
      | app f b => simp [tstep?] at h
      | bind x e₁ e₂ => simp [tstep?] at h
      | matchC s ctag ys b => simp [tstep?] at h
      | dup x e => simp [tstep?] at h
      | drop x e => simp [tstep?] at h
      | con0 ctag => simp [tstep?] at h
      | con1 ctag b => simp [tstep?] at h
      | con2 ctag b c => simp [tstep?] at h
      | store s i w => simp [tstep?] at h
  | c, hs, ρ, m, .matchC s ctag ys body, c', hs', ρ', m', e', h => by
      cases s with
      | var z =>
          cases hρ : ρ.lookup z with
          | none => simp [tstep?, hρ] at h
          | some r =>
              simp only [tstep?, hρ] at h
              by_cases hchk : ys.length = (CHeap.slotsAt c r).length && freeOf m ys
              · rw [ite_eq_left hchk] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                exact TStep.matchC hρ (of_decide_eq_true (Bool.and_eq_true_iff.mp hchk).1)
                  (freeOf_eq_true (Bool.and_eq_true_iff.mp hchk).2)
              · rw [ite_eq_right hchk] at h
                exact absurd h (by simp)
      | lam x body => simp [tstep?] at h
      | app f a => simp [tstep?] at h
      | bind x e₁ e₂ => simp [tstep?] at h
      | matchC s ctag ys body => simp [tstep?] at h
      | dup x e => simp [tstep?] at h
      | drop x e => simp [tstep?] at h
      | con0 ctag => simp [tstep?] at h
      | con1 ctag a => simp [tstep?] at h
      | con2 ctag a b => simp [tstep?] at h
      | store s i v => simp [tstep?] at h
  | c, hs, ρ, m, .store s i v, c', hs', ρ', m', e', h => by
      cases s with
      | var y =>
          cases hρ : ρ.lookup y with
          | none => simp [tstep?, hρ] at h
          | some r =>
              cases hv : claim? c hs ρ v with
              | none => simp [tstep?, hρ, hv] at h
              | some q =>
                  obtain ⟨c₁, hs₁, wv⟩ := q
                  simp only [tstep?, hρ, hv] at h
                  by_cases hchk : i < (CHeap.slotsAt c₁ r).length
                    && writeCheck c₁ r (storeSlots c₁ r i wv)
                  · rw [ite_eq_left hchk] at h
                    have hlen : i < (CHeap.slotsAt c₁ r).length :=
                      of_decide_eq_true (Bool.and_eq_true_iff.mp hchk).1
                    have hw : writeCheck c₁ r (storeSlots c₁ r i wv) = true :=
                      (Bool.and_eq_true_iff.mp hchk).2
                    by_cases h1 : CHeap.count c₁ r = 1
                    · rw [ite_eq_left h1] at h
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                      exact TStep.storeExclusive hρ (claim?_sound c hs ρ v c₁ hs₁ wv hv) hlen hw h1
                    · rw [ite_eq_right h1] at h
                      by_cases hm : 0 < (expand m).count r
                      · rw [ite_eq_left hm] at h
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                        exact TStep.storeShared hρ (claim?_sound c hs ρ v c₁ hs₁ wv hv) hlen hw hm h1
                      · rw [ite_eq_right hm] at h
                        exact absurd h (by simp)
                  · rw [ite_eq_right hchk] at h
                    exact absurd h (by simp)
      | lam x body => simp [tstep?] at h
      | app f a => simp [tstep?] at h
      | bind x e₁ e₂ => simp [tstep?] at h
      | matchC s ctag ys body => simp [tstep?] at h
      | dup x e => simp [tstep?] at h
      | drop x e => simp [tstep?] at h
      | con0 ctag => simp [tstep?] at h
      | con1 ctag a => simp [tstep?] at h
      | con2 ctag a b => simp [tstep?] at h
      | store s i v => simp [tstep?] at h
  | c, hs, ρ, m, .var x, c', hs', ρ', m', e', h => by simp [tstep?] at h
  | c, hs, ρ, m, .lam x body, c', hs', ρ', m', e', h => by simp [tstep?] at h
  | c, hs, ρ, m, .con0 ctag, c', hs', ρ', m', e', h => by simp [tstep?] at h
  | c, hs, ρ, m, .con1 ctag a, c', hs', ρ', m', e', h => by simp [tstep?] at h
  | c, hs, ρ, m, .con2 ctag a b, c', hs', ρ', m', e', h => by simp [tstep?] at h

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
