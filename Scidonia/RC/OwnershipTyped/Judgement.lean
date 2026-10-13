/-
The two judgements of the ownership discipline over the existing λPure syntax,
with no catch-all rule.

`Scidonia.RC.OwnershipTyped.Types` fixes the types, the tags and the quotation.
This module reads that fixed vocabulary as two *additional* `Prop`-valued
judgements over the existing `Expr`, beside the older `Scidonia.RC.Typed` and
without changing it:

* `Obs Γ e o` is the observation-only formation judgement: the terms that may
  stand where an observation is expected. Its rules are an observation variable
  of the context, the unit and the natural, and the empty-slot, full-slot and
  pair-of-slot-observations constructors. It admits no cell variable, no root
  constructor, no application, no read and no write — and every term it admits
  is a `RC.Value`, is of the source fragment, is of a description of the
  constructible fragment (which its variable rule carries as a condition), and
  binds no name.
* `WellTyped Γ e τ` is the fragment's typing: an observation, a root
  construction, a read, a write, and the two bindings — the cell hand-off and
  the observation binding. It tracks the source constructors, the tags, the
  arities, the binder freshness and the result types, and it promises *nothing*
  about uniqueness: two names may carry the same type, and a cell may be named
  by several names as far as `WellTyped` is concerned.
* `Own Γ κ e τ` is the ownership discipline. `κ` is *at most one* protected-cell
  owner — `none` or `held x` — a ghost index and not a run-time capability; it
  is a name, so it can name one holder and never two. `Own` entails `WellTyped`
  and `RC.Pure` (`own_wellTyped`, `own_pure`), so a program the discipline
  admits is a program of the source fragment.

**The rules of `Own`, and no catch-all.**

1. `obs`: an expression of `Obs Γ e o` is admitted as `.obs o` at the *unchanged*
   owner. An observation variable is therefore reusable and can never be
   promoted to a cell.
2. `fresh`: `.con1 rootTag a` is admitted as `.cell` only from `κ = none`, with
   `Obs Γ a slotObs`. The rule's conclusion pins the owner to `.none`, so a
   second root allocation while a cell is held is not derivable.
3. `read`: `.matchC (.var x) rootTag [y] body` is admitted as `.obs o` only at
   `κ = held x`, with `y` fresh in `Γ`, and with the body — the post-read
   continuation — admitted at the same owner. The match's single step borrows
   the cell and hands its *quotation* to `y`, so the read ends before the body
   runs, and the only read pattern is the known unary root tag.
4. `write`: `.store (.var x) 0 a` is admitted as `.cell` only at `κ = held x`,
   with `Obs Γ a slotObs`. It consumes the current handle and yields a new cell;
   the rule fixes the subject's shape and the index to `0`, so a second holder
   in the value or the subject and any other index are not derivable.
5. `cell-bind`: `.bind y e₁ e₂`, where `e₁` is admitted as `.cell` and `e₂` at
   the *fresh* owner `held y`, is admitted as `.obs o` at the unchanged owner.
   The two ways to be a `.cell` are `fresh` (no current cell) and `write`
   (consuming `held x`), so this is the explicit hand-off and not an ordinary
   let that would alias; the fresh name alone becomes the owner in the
   continuation.
6. `observation-bind`: an `Obs Γ e₁ o` binding a fresh name in a continuation is
   admitted as `.obs o'` at the *unchanged* owner, so a continuation cannot
   quietly run a write and then restore an obsolete owner.

**What is not admitted, and the refutations.** There is no rule for `.lam`,
`.app`, `dup`, `drop`, a cell variable as a value, a field matched as a cell,
cells under observation constructors, or an arbitrary store subject or index.
Each is a theorem about a specific expression or shape below —
`own_lam_absent`, `own_app_absent`, `own_dup_absent`, `own_drop_absent`,
`own_var_no_cell`, `own_var_absent`, `own_store_obs_absent`, `own_fresh_none`,
`own_fresh_held_absent`, `own_pair_cell_absent`, `own_alias_bind_absent`,
`own_store_self_absent`, `own_read_escape_absent` and the inversions
`own_cell_shape`, `own_bind_shape`, `own_read_shape` and `own_store_shape` —
proved by inverting the rules. Each stands beside an expression the rules *do*
admit: `own_fresh` is the root construction at an absent owner,
`own_transfer_bind` the hand-off that the aliasing binding is not,
`own_slot_store` the write of a slot observation where the self-write is not,
`own_read_slot_return` the detached observation the escape does not,
`own_observation_pair` the pair of two detached observations where the
cell-headed pair is not, and `own_cell_owner` the statement that a cell has at
most one owner.
-/
import Scidonia.RC.OwnershipTyped.Types

namespace Scidonia.RC

namespace OwnershipTyped

open Scidonia.FracPerm.StateVar.Layout5 (ObsDesc)

/-! ## The type context and the owner -/

/-- A type context: a partial map from names to types. A name is either absent
or has exactly one type, so no name holds two; the terms are finite, so only
finitely many names are ever bound. -/
abbrev TyEnv := Var → Option Ty

namespace TyEnv

/-- The empty context: no name has a type. -/
def empty : TyEnv := fun _ => none

/-- The context with `x` bound to `τ`, shadowing any type `x` had. -/
def extend (Γ : TyEnv) (x : Var) (τ : Ty) : TyEnv := fun z => if z = x then some τ else Γ z

/-- The empty context holds no name. -/
@[simp] theorem empty_apply (x : Var) : empty x = none := rfl

/-- The extended context holds the bound name. -/
@[simp] theorem extend_self (Γ : TyEnv) (x : Var) (τ : Ty) : (extend Γ x τ) x = some τ := by
  simp [extend]

/-- The extended context leaves every other name as the context had it. -/
theorem extend_of_ne {Γ : TyEnv} {x z : Var} {τ : Ty} (h : z ≠ x) :
    (extend Γ x τ) z = Γ z := by
  simp [extend, h]

/-- Extension is injective in the type it binds. -/
theorem extend_inj {Γ : TyEnv} {x : Var} {τ τ' : Ty} (h : extend Γ x τ = extend Γ x τ') :
    τ = τ' := by
  have h' := congrFun h x
  rw [extend_self, extend_self] at h'
  exact Option.some.inj h'

/-- A name the extended context does not hold the context does not hold either.
This is the step that makes a binder of one name irrelevant to the freshness of
every other name. -/
theorem extend_none_imp {Γ : TyEnv} {x z : Var} {τ : Ty} (h : (extend Γ x τ) z = none) :
    Γ z = none := by
  by_cases hzx : z = x
  · rw [hzx, extend_self] at h
    exact absurd h (by simp)
  · rwa [extend_of_ne hzx] at h

end TyEnv

/-- The owner of the protected cell: at most one, and a ghost index rather than
a run-time capability. -/
inductive Owner where
  /-- No protected cell is held. -/
  | none
  /-- The name `x` holds the protected cell. -/
  | held (x : Var)
deriving DecidableEq, Repr

/-- No name holds the cell, so `none` is not a held name: the two owners of the
index are distinct, which is what makes the owner at most one name. -/
theorem Owner.none_ne_held (x : Var) : (Owner.none : Owner) ≠ .held x := by
  intro h
  cases h

/-- Two held owners are equal only at one name. -/
theorem Owner.held_inj {x y : Var} (h : (Owner.held x : Owner) = .held y) : x = y := by
  cases h
  rfl

/-! ## The observation-only formation judgement -/

/-- The observation-only formation judgement: `e` may stand where an observation
of `o` is expected. Its six rules are an observation variable of the context, the
unit, the natural, the empty and full slots, and a pair of two slot
observations. It admits no cell variable, no root constructor, no application, no
mutable read, no write and no protected array; every term it admits is a λPure
value and of a description of the constructible fragment. -/
inductive Obs : TyEnv → Expr → ObsDesc → Prop where
  /-- An observation variable of the context is an observation of its type, when
  that type's description is of the constructible fragment. -/
  | var {Γ : TyEnv} (x : Var) {o : ObsDesc} (h : Γ x = some (.obs o)) (hf : Fragment o) :
      Obs Γ (.var x) o
  /-- The unit observation. -/
  | unit {Γ : TyEnv} : Obs Γ (.con0 unitTag) .unit
  /-- A natural observation. -/
  | nat {Γ : TyEnv} (n : Nat) : Obs Γ (.con0 n) .nat
  /-- The empty slot observation. -/
  | empty {Γ : TyEnv} : Obs Γ (.con0 emptyTag) slotObs
  /-- A full slot observation: the unary full tag applied to a natural. -/
  | full {Γ : TyEnv} (n : Nat) : Obs Γ (.con1 fullTag (.con0 n)) slotObs
  /-- A pair of two slot observations. -/
  | pair {Γ : TyEnv} {a b : Expr} (ha : Obs Γ a slotObs) (hb : Obs Γ b slotObs) :
      Obs Γ (.con2 pairTag a b) (.pair slotObs slotObs)

/-- Every observation the judgement admits is a λPure value. -/
theorem obs_value : ∀ {Γ : TyEnv} {e : Expr} {o : ObsDesc}, Obs Γ e o → Value e
  | _, _, _, .var _ _ _ => Value.var _
  | _, _, _, .unit => Value.con0 unitTag
  | _, _, _, .nat n => Value.con0 n
  | _, _, _, .empty => Value.con0 emptyTag
  | _, _, _, .full n => Value.con1 (Value.con0 n)
  | _, _, _, .pair ha hb => Value.con2 (obs_value ha) (obs_value hb)

/-- Every observation the judgement admits is of the constructible fragment,
which is the condition its variable rule carries. -/
theorem obs_fragment : ∀ {Γ : TyEnv} {e : Expr} {o : ObsDesc}, Obs Γ e o → Fragment o
  | _, _, _, .var _ _ hf => hf
  | _, _, _, .unit => Fragment.unit
  | _, _, _, .nat _ => Fragment.nat
  | _, _, _, .empty => Fragment.slot
  | _, _, _, .full _ => Fragment.slot
  | _, _, _, .pair _ _ => Fragment.pair_self

/-- Every observation the judgement admits is of the source fragment. -/
theorem obs_pure : ∀ {Γ : TyEnv} {e : Expr} {o : ObsDesc}, Obs Γ e o → Pure e
  | _, _, _, .var _ _ _ => Pure.var _
  | _, _, _, .unit => Pure.con0 unitTag
  | _, _, _, .nat n => Pure.con0 n
  | _, _, _, .empty => Pure.con0 emptyTag
  | _, _, _, .full n => Pure.con1 (Pure.con0 n)
  | _, _, _, .pair ha hb => Pure.con2 (obs_pure ha) (obs_pure hb)

/-- An observation binds no name: its rules are variables and constructors, and a
constructor binds nothing. -/
theorem obs_binders_nil : ∀ {Γ : TyEnv} {e : Expr} {o : ObsDesc}, Obs Γ e o → binders e = []
  | _, _, _, .var _ _ _ => rfl
  | _, _, _, .unit => rfl
  | _, _, _, .nat _ => rfl
  | _, _, _, .empty => rfl
  | _, _, _, .full _ => rfl
  | _, _, _, .pair ha hb => by simp [binders, obs_binders_nil ha, obs_binders_nil hb]

/-- An observation of a variable is its type in the context. -/
theorem obs_var_eq {Γ : TyEnv} {x : Var} {o : ObsDesc} (h : Obs Γ (.var x) o) :
    Γ x = some (.obs o) := by
  cases h with
  | var x h _ => exact h

/-! ## The typing -/

/-- The fragment's typing: the source constructor, its tags and arities, the
binder freshness and the result type, with no promise of uniqueness. Two names
may carry the same type and a cell may be named by several names as far as this
judgement is concerned; `Own` below is the discipline that adds the ownership
index. -/
inductive WellTyped : TyEnv → Expr → Ty → Prop where
  /-- An observation is typed as the observation of its description. -/
  | obs {Γ : TyEnv} {e : Expr} {o : ObsDesc} (h : Obs Γ e o) : WellTyped Γ e (.obs o)
  /-- A root construction is a cell, from an observation of a slot. -/
  | fresh {Γ : TyEnv} {a : Expr} (h : Obs Γ a slotObs) : WellTyped Γ (.con1 rootTag a) .cell
  /-- A read is an observation, its subject a cell name and its binder fresh. -/
  | read {Γ : TyEnv} (x y : Var) (body : Expr) {o : ObsDesc}
      (hx : Γ x = some .cell) (hy : Γ y = none)
      (h : WellTyped (Γ.extend y (.obs slotObs)) body (.obs o)) :
      WellTyped Γ (.matchC (.var x) rootTag [y] body) (.obs o)
  /-- A write is a cell, its subject a cell name and its index zero. -/
  | write {Γ : TyEnv} (x : Var) {a : Expr} (hx : Γ x = some .cell)
      (ha : Obs Γ a slotObs) : WellTyped Γ (.store (.var x) 0 a) .cell
  /-- A cell binding is an observation: its bound term a cell, its binder fresh,
  and its continuation typed at the fresh name as a cell. -/
  | cellBind {Γ : TyEnv} (y : Var) (e₁ e₂ : Expr) {o : ObsDesc}
      (h₁ : WellTyped Γ e₁ .cell) (hy : Γ y = none)
      (h₂ : WellTyped (Γ.extend y .cell) e₂ (.obs o)) :
      WellTyped Γ (.bind y e₁ e₂) (.obs o)
  /-- An observation binding is an observation at the fresh name's own
  description. -/
  | obsBind {Γ : TyEnv} (y : Var) (e₁ e₂ : Expr) {o o' : ObsDesc}
      (h₁ : Obs Γ e₁ o) (hy : Γ y = none)
      (h₂ : WellTyped (Γ.extend y (.obs o)) e₂ (.obs o')) :
      WellTyped Γ (.bind y e₁ e₂) (.obs o')

/-- Every typed term is of the source fragment. -/
theorem wt_pure : ∀ {Γ : TyEnv} {e : Expr} {τ : Ty}, WellTyped Γ e τ → Pure e := by
  intro Γ e τ h
  induction h with
  | obs hobs => exact obs_pure hobs
  | fresh hobs => exact Pure.con1 (obs_pure hobs)
  | read x y body hx hy hbody ih => exact Pure.matchC (Pure.var _) ih
  | write x hx ha => exact Pure.store (Pure.var _) (obs_pure ha)
  | cellBind y e₁ e₂ h₁ hy h₂ ih₁ ih₂ => exact Pure.bind ih₁ ih₂
  | obsBind y e₁ e₂ h₁ hy h₂ ih => exact Pure.bind (obs_pure h₁) ih

/-- A typed term binds no name the context already holds: the freshness the rules
ask of every binder, read off a derivation. The binder's own name is never
needed — each arm carries its binder's freshness in its own hypothesis, and the
rest is `TyEnv.extend_none_imp`. -/
theorem wt_binders_fresh : ∀ {Γ : TyEnv} {e : Expr} {τ : Ty},
    WellTyped Γ e τ → ∀ z, z ∈ binders e → Γ z = none := by
  intro Γ e τ h
  induction h with
  | obs hobs =>
      intro z hz
      rw [obs_binders_nil hobs] at hz
      exact absurd hz List.not_mem_nil
  | fresh hobs =>
      intro z hz
      simp [binders, obs_binders_nil hobs] at hz
  | read x y body hx hy hbody ih =>
      intro z hz
      rw [mem_binders_matchC] at hz
      rcases hz with hz | hz | hz
      · exact absurd hz (by simp [binders])
      · exact List.mem_singleton.mp hz ▸ hy
      · exact TyEnv.extend_none_imp (ih z hz)
  | write x hx ha =>
      intro z hz
      simp [binders, obs_binders_nil ha] at hz
  | cellBind y e₁ e₂ h₁ h₂ h₃ ih₁ ih₂ =>
      intro z hz
      rw [mem_binders_bind] at hz
      rcases hz with hz | hz | hz
      · exact hz ▸ h₂
      · exact ih₁ z hz
      · exact TyEnv.extend_none_imp (ih₂ z hz)
  | obsBind y e₁ e₂ h₁ h₂ h₃ ih =>
      intro z hz
      rw [mem_binders_bind] at hz
      rcases hz with hz | hz | hz
      · exact hz ▸ h₂
      · rw [obs_binders_nil h₁] at hz
        exact absurd hz List.not_mem_nil
      · exact TyEnv.extend_none_imp (ih z hz)

/-! ## The ownership discipline -/

/-- The ownership discipline: `e` is admitted as `τ` with `κ` the at most one
name holding the protected cell. The six rules are the observation, the root
construction, the read, the write and the two bindings, and there is no
catch-all. -/
inductive Own : TyEnv → Owner → Expr → Ty → Prop where
  /-- An observation is admitted at the unchanged owner. -/
  | obs {Γ : TyEnv} {κ : Owner} {e : Expr} {o : ObsDesc} (h : Obs Γ e o) :
      Own Γ κ e (.obs o)
  /-- A root construction is admitted as a cell only when no cell is held. -/
  | fresh {Γ : TyEnv} {a : Expr} (h : Obs Γ a slotObs) :
      Own Γ .none (.con1 rootTag a) .cell
  /-- A read is admitted only at the owner the subject names: the subject is a
  cell name, the binder is fresh, and the body — the post-read continuation — is
  admitted at the same owner. -/
  | read {Γ : TyEnv} (x y : Var) (body : Expr) {o : ObsDesc}
      (hx : Γ x = some .cell) (hy : Γ y = none)
      (h : Own (Γ.extend y (.obs slotObs)) (.held x) body (.obs o)) :
      Own Γ (.held x) (.matchC (.var x) rootTag [y] body) (.obs o)
  /-- A write is admitted only at the owner the subject names, on the subject's
  own name and at index zero. -/
  | write {Γ : TyEnv} (x : Var) {a : Expr} (hx : Γ x = some .cell)
      (ha : Obs Γ a slotObs) : Own Γ (.held x) (.store (.var x) 0 a) .cell
  /-- The cell hand-off: the bound term is a cell, the binder is fresh, and the
  continuation is admitted at the fresh name as the owner. The result is an
  observation at the unchanged owner. -/
  | cellBind {Γ : TyEnv} {κ : Owner} (y : Var) (e₁ e₂ : Expr) {o : ObsDesc}
      (h₁ : Own Γ κ e₁ .cell) (hy : Γ y = none)
      (h₂ : Own (Γ.extend y .cell) (.held y) e₂ (.obs o)) :
      Own Γ κ (.bind y e₁ e₂) (.obs o)
  /-- The observation binding: a value-producing observation bound to a fresh
  name, the continuation admitted at the unchanged owner. -/
  | obsBind {Γ : TyEnv} {κ : Owner} (y : Var) (e₁ e₂ : Expr) {o o' : ObsDesc}
      (h₁ : Obs Γ e₁ o) (hy : Γ y = none)
      (h₂ : Own (Γ.extend y (.obs o)) κ e₂ (.obs o')) :
      Own Γ κ (.bind y e₁ e₂) (.obs o')

/-! ## The ownership discipline entails the typing and the source fragment -/

/-- An admitted program is typed: the discipline's rules are the typing's rules
with the ownership index added. -/
theorem own_wellTyped : ∀ {Γ : TyEnv} {κ : Owner} {e : Expr} {τ : Ty},
    Own Γ κ e τ → WellTyped Γ e τ := by
  intro Γ κ e τ h
  induction h with
  | obs hobs => exact WellTyped.obs hobs
  | fresh hobs => exact WellTyped.fresh hobs
  | read x y body hx hy hbody ih => exact WellTyped.read x y body hx hy ih
  | write x hx ha => exact WellTyped.write x hx ha
  | cellBind y e₁ e₂ h₁ hy h₂ ih₁ ih₂ => exact WellTyped.cellBind y e₁ e₂ ih₁ hy ih₂
  | obsBind y e₁ e₂ h₁ hy h₂ ih => exact WellTyped.obsBind y e₁ e₂ h₁ hy ih

/-- An admitted program is of the source fragment: the discipline never admits a
`dup` or a `drop`. -/
theorem own_pure : ∀ {Γ : TyEnv} {κ : Owner} {e : Expr} {τ : Ty},
    Own Γ κ e τ → Pure e := by
  intro Γ κ e τ h
  induction h with
  | obs hobs => exact obs_pure hobs
  | fresh hobs => exact Pure.con1 (obs_pure hobs)
  | read x y body hx hy hbody ih => exact Pure.matchC (Pure.var _) ih
  | write x hx ha => exact Pure.store (Pure.var _) (obs_pure ha)
  | cellBind y e₁ e₂ h₁ hy h₂ ih₁ ih₂ => exact Pure.bind ih₁ ih₂
  | obsBind y e₁ e₂ h₁ hy h₂ ih => exact Pure.bind (obs_pure h₁) ih

/-- An admitted program binds no name the context already holds, which is what
makes an environment extension a substitution for exactly that name. -/
theorem own_binders_fresh : ∀ {Γ : TyEnv} {κ : Owner} {e : Expr} {τ : Ty},
    Own Γ κ e τ → ∀ z, z ∈ binders e → Γ z = none := by
  intro Γ κ e τ h
  induction h with
  | obs hobs =>
      intro z hz
      rw [obs_binders_nil hobs] at hz
      exact absurd hz List.not_mem_nil
  | fresh hobs =>
      intro z hz
      simp [binders, obs_binders_nil hobs] at hz
  | read x y body hx hy hbody ih =>
      intro z hz
      rw [mem_binders_matchC] at hz
      rcases hz with hz | hz | hz
      · exact absurd hz (by simp [binders])
      · exact List.mem_singleton.mp hz ▸ hy
      · exact TyEnv.extend_none_imp (ih z hz)
  | write x hx ha =>
      intro z hz
      simp [binders, obs_binders_nil ha] at hz
  | cellBind y e₁ e₂ h₁ h₂ h₃ ih₁ ih₂ =>
      intro z hz
      rw [mem_binders_bind] at hz
      rcases hz with hz | hz | hz
      · exact hz ▸ h₂
      · exact ih₁ z hz
      · exact TyEnv.extend_none_imp (ih₂ z hz)
  | obsBind y e₁ e₂ h₁ h₂ h₃ ih =>
      intro z hz
      rw [mem_binders_bind] at hz
      rcases hz with hz | hz | hz
      · exact hz ▸ h₂
      · rw [obs_binders_nil h₁] at hz
        exact absurd hz List.not_mem_nil
      · exact TyEnv.extend_none_imp (ih z hz)

/-- An admitted program binds no name the context already holds, one name at a
time: the form the substitution law is applied in. -/
theorem own_no_rebind {Γ : TyEnv} {κ : Owner} {e : Expr} {τ : Ty} {y : Var}
    (h : Own Γ κ e τ) (hne : Γ y ≠ none) : y ∉ binders e :=
  fun hm => hne (own_binders_fresh h y hm)

/-! ## What the rules cannot admit

Each refutation is an inversion of the rules of `Own`. The impossible rules are
never named: the index of the judgement and the head of the expression eliminate
them, so only the rules that could apply are inverted. -/

/-- A variable is never admitted as a cell: no rule of `Own` yields a `.cell`
from a variable, because the only shapes it admits as a cell are the root
construction and the write. -/
theorem own_var_no_cell (x : Var) : ∀ {Γ : TyEnv} {κ : Owner}, ¬ Own Γ κ (.var x) .cell := by
  intro Γ κ h
  cases h

/-- A variable whose name the context types as a cell is admitted at no type at
all: it is neither an observation (its type is not an observation) nor a cell. -/
theorem own_var_absent {Γ : TyEnv} {x : Var} {τ : Ty} (hx : Γ x = some .cell) :
    ∀ {κ : Owner}, ¬ Own Γ κ (.var x) τ := by
  intro κ h
  cases h with
  | obs hobs =>
      have h' := obs_var_eq hobs
      rw [hx] at h'
      exact absurd h' (by simp)

/-- A cell binding whose bound term is a name is not admitted: the two ways to be
a cell are the root construction and the write, and neither is a name. This is
the aliasing the hand-off refuses, and `own_transfer_bind` is the transfer the
same shape admits. -/
theorem own_alias_bind_absent {Γ : TyEnv} {x y : Var} {e₂ : Expr} {τ : Ty}
    (hx : Γ x = some .cell) : ∀ {κ : Owner}, ¬ Own Γ κ (.bind y (.var x) e₂) τ := by
  intro κ h
  cases h with
  | obs hobs => cases hobs
  | cellBind _ _ _ h₁ _ _ => exact own_var_no_cell x h₁
  | obsBind _ _ _ h₁ _ _ =>
      have h' := obs_var_eq h₁
      rw [hx] at h'
      exact absurd h' (by simp)

/-- A write of a name as its own value is not admitted when the context types
that name as a cell: the written value would have to be a slot observation, and
a cell name is not one. `own_slot_store` is the same write with a slot
observation as its value. -/
theorem own_store_self_absent {Γ : TyEnv} {x : Var} (hx : Γ x = some .cell) :
    ∀ {κ : Owner} {τ : Ty}, ¬ Own Γ κ (.store (.var x) 0 (.var x)) τ := by
  intro κ τ h
  cases h with
  | obs hobs => cases hobs
  | write _ _ ha =>
      have h' := obs_var_eq ha
      rw [hx] at h'
      exact absurd h' (by simp)

/-- A read whose continuation returns the cell's own name is not admitted: an
`.obs`-typed body must be an observation, and the name is typed as a cell.
`own_read_slot_return` returns the detached observation the read binds instead,
and `own_read_shape` is the read rule's own shape. -/
theorem own_read_escape_absent {Γ : TyEnv} {x y : Var} {τ : Ty}
    (hx : Γ x = some .cell) : ∀ {κ : Owner},
    ¬ Own Γ κ (.matchC (.var x) rootTag [y] (.var x)) τ := by
  intro κ h
  cases h with
  | obs hobs => cases hobs
  | read x y _ _ hy hbody =>
      have hxc : (Γ.extend y (.obs slotObs)) x = some .cell := by
        by_cases hxy : x = y
        · have hxy' : Γ y = some .cell := by rw [← hxy]; exact hx
          rw [hxy'] at hy
          exact absurd hy (by simp)
        · rw [TyEnv.extend_of_ne hxy]
          exact hx
      exact own_var_absent hxc hbody

/-- A pair whose first component is the cell's name is not admitted: the pair
rule's components are slot observations, and a cell name is not one.
`own_observation_pair` is the pair of two detached observations. -/
theorem own_pair_cell_absent {Γ : TyEnv} {x : Var} {b : Expr} (hx : Γ x = some .cell) :
    ∀ {κ : Owner} {τ : Ty}, ¬ Own Γ κ (.con2 pairTag (.var x) b) τ := by
  intro κ τ h
  cases h with
  | obs hobs =>
      cases hobs with
      | pair ha _ =>
          have h' := obs_var_eq ha
          rw [hx] at h'
          exact absurd h' (by simp)

/-- A root construction is admitted as a cell only when no cell is held: the
`fresh` rule's own owner is `none`. -/
theorem own_fresh_none {Γ : TyEnv} {a : Expr} {κ : Owner}
    (h : Own Γ κ (.con1 rootTag a) .cell) : κ = .none := by
  cases h with
  | fresh _ => rfl

/-- A second root allocation while a cell is held is not admitted: the root
construction's owner is `none` and a held owner is not. -/
theorem own_fresh_held_absent {Γ : TyEnv} {a : Expr} {x : Var} :
    ¬ Own Γ (.held x) (.con1 rootTag a) .cell := by
  intro h
  exact Owner.none_ne_held x (own_fresh_none h).symm

/-- A write is admitted as a cell only at the subject's own name, at index zero,
with a slot observation as its value: the write rule fixes all three, so an
arbitrary store subject or index is not derivable. -/
theorem own_store_shape {Γ : TyEnv} {s : Expr} {i : Nat} {a : Expr} {κ : Owner} {τ : Ty}
    (h : Own Γ κ (.store s i a) τ) :
    ∃ x, s = .var x ∧ i = 0 ∧ τ = .cell ∧ κ = .held x ∧ Obs Γ a slotObs := by
  cases h with
  | obs hobs => cases hobs
  | write x hx ha => exact ⟨x, rfl, rfl, rfl, rfl, ha⟩

/-- A write is never admitted as an observation: no rule of `Own` yields an
`.obs` type from a store. -/
theorem own_store_obs_absent {Γ : TyEnv} {s : Expr} {i : Nat} {a : Expr} {o : ObsDesc}
    {κ : Owner} : ¬ Own Γ κ (.store s i a) (.obs o) := by
  intro h
  cases h with
  | obs hobs => cases hobs

/-- The only two ways to be a cell are the root construction and the write: the
inversion the hand-off's discipline is read from. -/
theorem own_cell_shape {Γ : TyEnv} {κ : Owner} {e : Expr} (h : Own Γ κ e .cell) :
    (∃ a, e = .con1 rootTag a ∧ κ = .none ∧ Obs Γ a slotObs)
      ∨ (∃ x a, e = .store (.var x) 0 a ∧ κ = .held x ∧ Obs Γ a slotObs) := by
  cases h with
  | fresh hobs => exact Or.inl ⟨_, rfl, rfl, hobs⟩
  | write x hx ha => exact Or.inr ⟨x, _, rfl, rfl, ha⟩

/-- A cell has at most one owner: two admissions of the same expression as a cell
carry the same owner, which is the index's "at most one holder" read off the
rules. -/
theorem own_cell_owner {Γ : TyEnv} {κ κ' : Owner} {e : Expr}
    (h : Own Γ κ e .cell) (h' : Own Γ κ' e .cell) : κ = κ' := by
  cases h with
  | fresh _ =>
      cases h' with
      | fresh _ => rfl
  | write _ _ _ =>
      cases h' with
      | write _ _ _ => rfl

/-- A binding admitted as an observation is admitted by one of the two binding
rules: either the hand-off — a `.cell` bound term, a fresh binder and a
continuation admitted at the fresh owner — or an observation binding at the
unchanged owner. -/
theorem own_bind_shape {Γ : TyEnv} {κ : Owner} {y : Var} {e₁ e₂ : Expr} {o : ObsDesc}
    (h : Own Γ κ (.bind y e₁ e₂) (.obs o)) :
    ((∃ κ₁, Own Γ κ₁ e₁ .cell) ∧ Γ y = none ∧
        Own (Γ.extend y .cell) (.held y) e₂ (.obs o))
      ∨ (∃ o₁, Obs Γ e₁ o₁ ∧ Γ y = none ∧
          Own (Γ.extend y (.obs o₁)) κ e₂ (.obs o)) := by
  cases h with
  | obs hobs => cases hobs
  | cellBind y e₁ e₂ h₁ hy h₂ => exact Or.inl ⟨⟨_, h₁⟩, hy, h₂⟩
  | obsBind y e₁ e₂ h₁ hy h₂ => exact Or.inr ⟨_, h₁, hy, h₂⟩

/-- A read is admitted only with the unary root tag and one binder, at the
subject's own owner: the shape the rule fixes, read off a derivation. -/
theorem own_read_shape {Γ : TyEnv} {κ : Owner} {s : Expr} {c : Ctor} {ys : List Var}
    {body : Expr} {τ : Ty} (h : Own Γ κ (.matchC s c ys body) τ) :
    ∃ x y o, s = .var x ∧ c = rootTag ∧ ys = [y] ∧ τ = .obs o ∧
      Γ x = some .cell ∧ Γ y = none ∧ κ = .held x ∧
      Own (Γ.extend y (.obs slotObs)) (.held x) body (.obs o) := by
  cases h with
  | obs hobs => cases hobs
  | read x y body hx hy hbody => exact ⟨x, y, _, rfl, rfl, rfl, rfl, hx, hy, rfl, hbody⟩

/-- An abstraction is admitted at no type: there is no rule for `.lam`, so the
discipline is not a higher-order one. -/
theorem own_lam_absent (x : Var) (body : Expr) :
    ∀ {Γ : TyEnv} {κ : Owner} {τ : Ty}, ¬ Own Γ κ (.lam x body) τ := by
  intro Γ κ τ h
  cases h with
  | obs hobs => cases hobs

/-- An application is admitted at no type: there is no rule for `.app`. -/
theorem own_app_absent (f a : Expr) :
    ∀ {Γ : TyEnv} {κ : Owner} {τ : Ty}, ¬ Own Γ κ (.app f a) τ := by
  intro Γ κ τ h
  cases h with
  | obs hobs => cases hobs

/-- A `dup` instruction is admitted at no type: the discipline is over the source
fragment, which has no `dup`. -/
theorem own_dup_absent (x : Var) (e : Expr) :
    ∀ {Γ : TyEnv} {κ : Owner} {τ : Ty}, ¬ Own Γ κ (.dup x e) τ := by
  intro Γ κ τ h
  cases h with
  | obs hobs => cases hobs

/-- A `drop` instruction is admitted at no type, for the same reason. -/
theorem own_drop_absent (x : Var) (e : Expr) :
    ∀ {Γ : TyEnv} {κ : Owner} {τ : Ty}, ¬ Own Γ κ (.drop x e) τ := by
  intro Γ κ τ h
  cases h with
  | obs hobs => cases hobs

/-! ## The accepted expressions beside the refutations -/

/-- A root construction is admitted as a cell when no cell is held. -/
theorem own_fresh {Γ : TyEnv} {a : Expr} (h : Obs Γ a slotObs) :
    Own Γ .none (.con1 rootTag a) .cell :=
  Own.fresh h

/-- The transfer: a binding whose bound term is a write through the held name is
admitted, the fresh name becoming the owner in the continuation. This is the
shape the aliasing binding is refused at. -/
theorem own_transfer_bind {Γ : TyEnv} {x y : Var} {a e₂ : Expr} {o : ObsDesc}
    (hx : Γ x = some .cell) (hy : Γ y = none) (ha : Obs Γ a slotObs)
    (h₂ : Own (Γ.extend y .cell) (.held y) e₂ (.obs o)) :
    Own Γ (.held x) (.bind y (.store (.var x) 0 a) e₂) (.obs o) :=
  Own.cellBind y (.store (.var x) 0 a) e₂ (Own.write x hx ha) hy h₂

/-- A write of a slot observation is admitted: the value is a quotation of a slot
and not the cell's name. -/
theorem own_slot_store {Γ : TyEnv} {x : Var} {a : Expr} (hx : Γ x = some .cell)
    (ha : Obs Γ a slotObs) : Own Γ (.held x) (.store (.var x) 0 a) .cell :=
  Own.write x hx ha

/-- A read whose continuation returns the observation it binds is admitted: the
bound name is the detached quotation of the cell's slot, and the owner is the
subject's. -/
theorem own_read_slot_return {Γ : TyEnv} {x y : Var} {e₂ : Expr} {o : ObsDesc}
    (hx : Γ x = some .cell) (hy : Γ y = none)
    (h₂ : Own (Γ.extend y (.obs slotObs)) (.held x) e₂ (.obs o)) :
    Own Γ (.held x) (.matchC (.var x) rootTag [y] e₂) (.obs o) :=
  Own.read x y e₂ hx hy h₂

/-- A pair of two detached slot observations is an observation: neither component
is the cell's name. -/
theorem own_observation_pair {Γ : TyEnv} {κ : Owner} {a b : Var}
    (ha : Γ a = some (.obs slotObs)) (hb : Γ b = some (.obs slotObs)) :
    Own Γ κ (.con2 pairTag (.var a) (.var b)) (.obs (.pair slotObs slotObs)) :=
  Own.obs (Obs.pair (Obs.var a ha Fragment.slot) (Obs.var b hb Fragment.slot))

end OwnershipTyped

end Scidonia.RC
