/-
A single-root logical heap, and the read and write transitions over it.

`Scidonia.FracPerm.StateVar.Model` runs its program recipes against a state
`σ` alone: a `PConf` carries one state and a `write` step replaces it. This
module adds the other half of the picture, a *logical* heap `Loc → Option σ` in
which one root cell at `ℓ` holds the state and every other cell is untouched.
`At ℓ s h` says the cell at `ℓ` holds `s`; `ReadAt` and `WriteAt` are the
transitions a read and a write make to that cell.

The heap is a *simulation* of the pure model, not a second execution model:

* `read_at_no_store` and `read_at_detached`: a read returns what the instance
  observes and leaves the heap alone, and what it returns encodes without a
  reference to the root it read.
* `write_at_valid`, `write_at_frame` and `snapshot_after_write`: a write leaves
  a valid state in the root cell, changes no other cell, and a later read of the
  same root observes the replacement — with the old observation bound to the
  *pre-write* cell and the new one to the *post-write* cell.
* `readAt_step_observe` and `pstep_write_corresponds`: the heap transitions and
  the pure `Step`/`PStep` transitions describe the same logical change, so the
  heap does not overstate what the model proves.

What this does **not** say: writing is a new heap value, not physical mutation;
there is no address preservation, no fixed-layout tag or payload update, and no
separation algebra. The fractions here are M1's: a share is a `Rat` in
`(0, 1]`, a split is a halving, and a full share admits no further reader
(`cannot_add_reader`). None of this certifies Lean's runtime representation; the
array's in-place evidence stays the run-time harness (`ScidoniaInPlace`).

One root is all this heap models. Several cells, or true `IO` mutation, would
be a different model with different theorems — a separation algebra, or a
statement about addresses — and neither is claimed here.
-/
import Scidonia.FracPerm.StateVar.Model

namespace Scidonia.FracPerm.StateVar

/-- A logical heap: each root cell holds a state, or nothing.

`h ℓ = some s` says the cell at `ℓ` holds `s`; a cell that is `none` holds
nothing. Nothing here says how many cells a session uses: the model's programs
name one root. -/
abbrev Heap (σ : Type) := Loc → Option σ

/-- The cell at `ℓ` holds `s`. -/
def At {σ : Type} (ℓ : Loc) (s : σ) (h : Heap σ) : Prop := h ℓ = some s

/-- The heap with the cell at `ℓ` set to `v`, leaving every other cell alone.

The heap carries its own point update so that a write's effect on one root, and
its effect on every other root, are both statements about this definition:
`Heap.update_self` reads the cell back, and `Heap.update_of_ne` is the frame
argument. -/
def Heap.update (h : Heap σ) (ℓ : Loc) (v : Option σ) : Heap σ :=
  fun m => if m = ℓ then v else h m

/-- An update is read back at the cell it set. -/
theorem Heap.update_self (h : Heap σ) (ℓ : Loc) (v : Option σ) :
    Heap.update h ℓ v ℓ = v := by
  unfold Heap.update
  simp

/-- An update leaves every other cell alone. -/
theorem Heap.update_of_ne {h : Heap σ} {ℓ m : Loc} (hm : m ≠ ℓ) (v : Option σ) :
    Heap.update h ℓ v m = h m := by
  unfold Heap.update
  simp [hm]

/-- A read of the root cell at `ℓ`: the cell holds a valid `s`, the value is
exactly what the instance observes of it, and the heap is unchanged.

The read result is the operation's own result type, so a read of one operation
cannot observe another's result. -/
def ReadAt {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp)
    (ℓ : Loc) (o : ReadOp) (h h' : Heap σ) (v : inst.Result o) : Prop :=
  ∃ s, At ℓ s h ∧ inst.Valid s ∧ h' = h ∧ v = inst.observe o s

/-- A write to the root cell at `ℓ`: the cell holds a valid `s`, the new heap is
the old one with that cell replaced by the instance's replacement, no other cell
changes, and the boolean is what the instance's `replace` reported.

This is a logical replacement: the old value is not destroyed, and the new heap
is a new function. -/
def WriteAt {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp)
    (ℓ : Loc) (w : WriteOp) (h h' : Heap σ) (b : Bool) : Prop :=
  ∃ s, At ℓ s h ∧ inst.Valid s ∧
    h' = Heap.update h ℓ (some (inst.replace w s).1) ∧
    b = (inst.replace w s).2

section
variable {σ Init ReadOp WriteOp : Type} [inst : LawfulStateVar σ Init ReadOp WriteOp]

/-- A read leaves the heap alone. -/
theorem read_at_no_store {ℓ : Loc} {o : ReadOp} {h h' : Heap σ} {v : inst.Result o}
    (hr : ReadAt inst ℓ o h h' v) : h' = h := by
  obtain ⟨_, _, _, hh, _⟩ := hr
  exact hh

/-- What a read returns is detached from the root it read: the heap transition
inherits the instance's no-reference law. -/
theorem read_at_detached {ℓ : Loc} {o : ReadOp} {h h' : Heap σ} {v : inst.Result o}
    (hr : ReadAt inst ℓ o h h' v) : NoRef ℓ (inst.encodeRead o v) := by
  obtain ⟨s, _, hvalid, _, hv⟩ := hr
  rw [hv]
  exact inst.observe_detached ℓ o s hvalid

/-- A cell holds at most one state: two states read from the same cell of the
same heap are the same state. -/
theorem read_agreement {ℓ : Loc} {s t : σ} {h : Heap σ}
    (hs : At ℓ s h) (ht : At ℓ t h) : s = t := by
  unfold At at hs ht
  rw [hs] at ht
  exact Option.some.inj ht

/-- A write leaves the cell holding an admissible state: the instance's
`replace_valid`, at the heap's root. -/
theorem write_at_valid {ℓ : Loc} {w : WriteOp} {h h' : Heap σ} {b : Bool}
    (hw : WriteAt inst ℓ w h h' b) : ∃ s', At ℓ s' h' ∧ inst.Valid s' := by
  obtain ⟨s, hat, hvalid, hh', _⟩ := hw
  refine ⟨(inst.replace w s).1, ?_, inst.replace_valid w s hvalid⟩
  unfold At at hat ⊢
  rw [hh', Heap.update_self]

/-- A write changes no cell other than its root. -/
theorem write_at_frame {ℓ m : Loc} {w : WriteOp} {h h' : Heap σ} {b : Bool}
    (hw : WriteAt inst ℓ w h h' b) (hm : m ≠ ℓ) : h' m = h m := by
  obtain ⟨_, _, _, hh', _⟩ := hw
  rw [hh', Heap.update_of_ne hm]

/-- The read–write–read snapshot: a read of a root cell, then a write to it, then
a read of it again yields the *post-write* cell's observation, while the first
read's value is bound to the *pre-write* cell — the two observations are tied to
their respective heap states, not merely to positions in a trace. -/
theorem snapshot_after_write {ℓ : Loc} {o : ReadOp} {w : WriteOp} {h h' : Heap σ}
    {b : Bool} {v v' : inst.Result o}
    (hr : ReadAt inst ℓ o h h v) (hw : WriteAt inst ℓ w h h' b)
    (hr' : ReadAt inst ℓ o h' h' v') :
    ∃ s, At ℓ s h ∧ v = inst.observe o s ∧
      v' = inst.observe o (inst.replace w s).1 := by
  obtain ⟨s, hat, _, _, hv⟩ := hr
  obtain ⟨s₀, hat₀, _, hh', _⟩ := hw
  have hss : s₀ = s := read_agreement hat₀ hat
  rw [hss] at hh'
  obtain ⟨s₁, hat₁, _, _, hv'⟩ := hr'
  refine ⟨s, hat, hv, ?_⟩
  have hcell : h' ℓ = some (inst.replace w s).1 := by rw [hh', Heap.update_self]
  have hs₁ : s₁ = (inst.replace w s).1 := by
    unfold At at hat₁
    exact Option.some.inj (hat₁.symm.trans hcell)
  rw [hv', hs₁]

/-- The heap transition of a `PStep.write` step, given a heap whose root holds
the configuration's state, is a `WriteAt`: the pure model's state change and the
root cell's replacement are the same logical change. This is a correspondence
between two descriptions of one transition, not a claim about machine memory. -/
theorem pstep_write_corresponds {α : Type} {s : σ} {w : WriteOp} {k : Bool → PT inst α}
    {ℓ : Loc} {h h' : Heap σ} {c' : PConf inst}
    (hstep : PStep inst (.exclusive s (.write w k)) c') (hat : At ℓ s h)
    (hs : inst.Valid s) (hh' : h' = Heap.update h ℓ (some (inst.replace w s).1)) :
    c' = .exclusive (inst.replace w s).1 (k (inst.replace w s).2) ∧
      WriteAt inst ℓ w h h' (inst.replace w s).2 :=
  ⟨write_step hstep, ⟨s, hat, hs, hh', rfl⟩⟩

/-- The heap read transition and the model's `read` step hand the continuation
the same value: a `ReadAt` of the root that holds `s` is exactly a `Step` that
observes `s`. -/
theorem readAt_step_observe {ℓ : Loc} {s : σ} {q : Rat} {o : ReadOp}
    {k : inst.Result o → RT inst α} {h h' : Heap σ} {v : inst.Result o}
    (hat : At ℓ s h) (hr : ReadAt inst ℓ o h h' v) :
    Step inst s (.run q (.read o k)) (.run q (k v)) := by
  obtain ⟨s₀, hat₀, _, _, hv⟩ := hr
  have hss : s₀ = s := read_agreement hat₀ hat
  rw [hss] at hv
  rw [hv]
  exact Step.read

/-! ## Shares

M1's fraction reasoning, at the single root: a share is a `Rat` in `(0, 1]`, two
holders of the same cell may hold shares that fit in the whole, a fork halves a
share, and a full share admits no further reader. This is deliberately not a
standalone resource algebra and says nothing about separation-logic
bi-entailment. -/

/-- A share is a positive fraction of at most the whole. -/
def ValidShare (q : Rat) : Prop := 0 < q ∧ q ≤ 1

/-- Two holders of the same root cell, with shares that fit in the whole and a
state actually in that cell. -/
structure SameRootShare {σ : Type} (ℓ : Loc) (h : Heap σ) (p q : Rat) : Prop where
  /-- The left holder's share is valid. -/
  left_valid : ValidShare p
  /-- The right holder's share is valid. -/
  right_valid : ValidShare q
  /-- The two shares fit in the whole. -/
  fit : p + q ≤ 1
  /-- The cell both holders hold. -/
  rooted : ∃ s, At ℓ s h

/-- Halving a valid share gives two valid halves: a fork's two branches each run
at half the parent's share. -/
theorem half_valid {q : Rat} (hq : ValidShare q) : ValidShare (q / 2) := by
  obtain ⟨h1, h2⟩ := hq
  exact ⟨by grind, by grind⟩

/-- Rejoining two halves restores the parent's share: the two branches of a fork
hold between them exactly what the fork held. -/
theorem halves_rejoin (q : Rat) : q / 2 + q / 2 = q := by grind

/-- A share of the whole leaves nothing for another reader: once one holder owns
all of the cell, no further positive share fits beside it. This is what makes a
read phase's share `1` exclude a concurrent writer. -/
theorem cannot_add_reader (q : Rat) (hq : 0 < q) : ¬ (1 + q ≤ (1 : Rat)) := by grind

end

end Scidonia.FracPerm.StateVar
