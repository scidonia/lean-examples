/-
The ownership discipline of the layout-indexed tree, over the existing λPure
syntax, with no catch-all rule.

`Scidonia.RC.TreeOwnership.Quote` writes a `Layout5.State` as a λPure term and
resolves a path into it, and `Scidonia.RC.TreeOwnership.Spine` accounts the
fractional authority of the readers and writers of its nodes. This module reads
those two as one *judgement* over the same `Expr`, beside the older
`Scidonia.RC.OwnershipTyped.Own` and the existing typing, changing neither:

`TreeOwn d Γ ρ A s e τ v s'` admits the term `e` at the tree type `τ`, holding
the λPure value `v`, from the state `s` to the state `s'`, in the handle context
`Γ`, under the observation environment `ρ` and the per-node account `A`.

**The value index.** The tree fragment's result values are not readable off the
state: the library's own layout state hides its leaf content behind private
traversals, and the only public read of it is the behavioural `read?`. So the
value a term produces is an index of the judgement and each rule *names* it, and
the executable interpreter of the following module computes exactly that term.
An observation is admitted at the instance `inst ρ e`; a read at the observation
its continuation was handed; a write at the root node of the observation written;
a subtree replacement at the struct node of the operand's quotation; and a
binding at whatever its continuation produced.

**The two invariants.** Every rule carries *both* standing conditions of the
discipline, so no derivation can exist without them:

* the account is valid (`ValidAccount`): every lent share is a positive fraction
  of at most the whole, a node's shares fit in it, a node's ledger names each
  loan once and no node appears twice. A rule's write right (`WriteHolds`) and a
  read's loans (`ReadLoan`) are read *at those same nodes* against it, so an
  overfull account admits nothing.
* the handle context is well formed (`HandleWF`): one protected path has one live
  name. Two names holding nodes at one path are one name, so the discipline
  cannot hand one subtree's authority to two names.

**The handles.** A *handle* is the protected node a name holds: `NodeTy.at w p l
h` is the node at the path `p` whose end is `l`, and `NodeTy.spine w p a h skip`
is the spine of the array at `p` from the offset `skip` — the tail a `cons` match
hands to its second binder, which is not a path of its own. The ghost identifier
`w` is the *holder*: every name of one client carries it, so the account's
entries at one node are that node's holders, and the read and write rights below
compare holdings at the same node.

**The state and the environment.** The judgment is indexed by the state it starts
at and the state it leaves, so an admitted write carries its own success — its
`setLeaf` reports it, and its `setStructLeft` reports `some` only where the path
addresses a node — and the nested replacement names the state it inspects. The
environment carries the value each name holds: for a handle, the node value the
rules below read their fields from; for an observation, its detached quotation. A
handle a write was performed through is *spent*: the hand-off rule removes its
name from the continuation's context, so a second use of it is not derivable.

**The rules, and no catch-all.**

1. `obs`: an expression of `Obs (obsEnv Γ) e o` is admitted as `.obs o`, holding
   its instance, at the unchanged state, context, environment and account.
   `obsEnv` lowers the tree context to the one-cell fragment's — a node name
   becomes a `cell` name, which `Obs` refuses — so a node name is never an
   observation.
2. `read`: `.matchC (.var x) rootTag [y] body` is admitted as the continuation's
   type and value when `x` holds a leaf node, the environment's value there is
   the unary root node of an observation quotation, and the state's read at the
   node's path — read under the reader's own borrow `ReadLoan`, whose identifier
   is the node's holder — returns the encoding of exactly the element that
   quotation holds. The continuation runs with `y` bound to the *detached*
   quotation, and nothing of the node reaches it.
3. `write`: `.store (.var x) 0 a` is admitted at `x`'s leaf node, holding the
   root node of the instance of `a`, when `a` is an observation of the leaf's
   description and the account admits a write there (`WriteHolds`). The state it
   leaves is the library's own leaf write, and it reports success.
4. `writeSub`: the same write at a *struct* node is admitted when its operand's
   instance is a `Recipe` of the struct's left component: a freshly built node
   quotation, never a client-held state. The state it leaves is the struct's own
   cell with that component replaced, and the rule carries that replacement's
   own success: `setStructLeft` answers `some` only where every index on the path
   addresses an element, and answers `none` — refusing the derivation — at an
   index that addresses nothing.
5. `descendStruct`: `.matchC (.var x) structTag [y, z] body` is admitted when
   `x` holds a struct node and the environment's value there is the struct node
   of two field values: the continuation runs with `y` and `z` holding the two
   components' nodes — both under `x`'s holder and both separately accounted —
   and with those two values.
6. `descendSpine`: `.matchC (.var x) consTag [y, z] body` is admitted when `x`
   holds a spine and the environment's value there is the cons node of a head
   and a tail value: `y` holds the element at the spine's offset and `z` holds
   the rest of the spine, whose offset is one further on.
7. `handoff`: `.bind y e₁ e₂` is admitted when `e₁` is admitted as the node `n`
   with the value `v₁`: the continuation runs with `y` holding `n` — the fresh
   name's value being `v₁` — and with the context of the name `x` the term was
   written through *removed*. The stale handle is not derivable afterwards, and
   the continuation is well formed exactly because the removed name was the
   subtree's only live one.
8. `obsBind`: `.bind y e₁ e₂` where `e₁` is admitted as an observation runs the
   continuation with `y` holding that observation's value, at the unchanged
   holder and the unchanged account.

**What is refused.** There is no rule for a read whose node is not a leaf, none
for a write at a node another holder reads, none for a second write through a
spent handle, none for a write handed two names of one subtree, none for a
nonleaf replacement at an index the state does not have, and none for an
observation-typed use of a node. The refusals below are `¬ TreeOwn` statements
for specific expressions, proved by inverting the rules, each beside a
same-purpose expression the rules do accept.
-/
import Scidonia.RC.TreeOwnership.Quote
import Scidonia.RC.TreeOwnership.Spine

namespace Scidonia.RC

namespace TreeOwnership

open Scidonia.FracPerm.StateVar (Slot)
open Scidonia.FracPerm.StateVar.Layout5
open Scidonia.RC.OwnershipTyped (Ty TyEnv Obs Denote Fragment VEnv inst rootTag)

/-! ## The handles -/

/-- The protected node a name holds: a leaf node at the path `p` whose end is the
description `o`, a struct node at the path `p`, or — when `p` ends at an array —
the spine of that array from the offset `k`, the tail a `cons` match hands on. The
identifier `w` is the holder, not the node: two names of one client carry the same
one, and the account's entries at a node are that node's holders. -/
inductive NodeTy : Layout → Type where
  /-- The node at `p`, whose end is the layout `l`, held under `w`. -/
  | at (w : Nat) (p : Path d) (l : Layout) (h : At p = l) : NodeTy d
  /-- The spine of the array `p` ends at, from the offset `k`, held under `w`. -/
  | spine (w : Nat) (p : Path d) (a : Layout) (h : At p = .arr a) (skip : Nat) : NodeTy d

/-- The path of a handle: the path its node is at. -/
def NodeTy.path {d : Layout} : NodeTy d → Path d
  | .at _ p _ _ => p
  | .spine _ p _ _ _ => p

/-- The layout a handle's node ends at: the leaf's description, the struct's two
components' layout, or an array's. -/
def NodeTy.layout {d : Layout} : NodeTy d → Layout
  | .at _ _ l _ => l
  | .spine _ _ a _ _ => .arr a

/-- The holder of a handle. -/
def NodeTy.holder {d : Layout} : NodeTy d → Nat
  | .at w _ _ _ => w
  | .spine w _ _ _ _ => w

/-- The layout a path's end is reached from: appending a path to another does not
change what the appended path ends at. -/
theorem At_append : ∀ {d : Layout} (p : Path d) (q : Path (At p)), At (Path.append p q) = At q
  | _, .here, _ => rfl
  | _, .left p, q => At_append p q
  | _, .right p, q => At_append p q
  | _, .index _ p, q => At_append p q

/-- Casting a path along an equality of layouts does not change what it ends at:
the cast is a change of type alone. -/
theorem At_cast {d d' : Layout} (e : d = d') (r : Path d) :
    At (cast (congrArg Path e) r) = At r := by
  cases e
  rfl

/-- The path to a struct node's left component. -/
def leftPath {d : Layout} (p : Path d) {a b : Layout} (h : At p = .struct a b) : Path d :=
  Path.append p (cast (congrArg Path h.symm) (.left (.here : Path a)))

/-- The path to a struct node's right component. -/
def rightPath {d : Layout} (p : Path d) {a b : Layout} (h : At p = .struct a b) : Path d :=
  Path.append p (cast (congrArg Path h.symm) (.right (.here : Path b)))

/-- The path to the head of the spine of an array from an offset. -/
def headPath {d : Layout} (p : Path d) (a : Layout) (h : At p = .arr a) (k : Nat) : Path d :=
  Path.append p (cast (congrArg Path h.symm) (.index k (.here : Path a)))

/-- The left component's path ends at the left component: the layout a descent
into a struct node's left component is at. -/
theorem leftPath_at {d : Layout} (p : Path d) {a b : Layout} (h : At p = .struct a b) :
    At (leftPath p h) = a := by
  have hA := At_append p (cast (congrArg Path h.symm) (.left (.here : Path a)))
  have hB := At_cast h.symm (.left (.here : Path a))
  simp only [leftPath, hA, hB]

/-- The right component's path ends at the right component. -/
theorem rightPath_at {d : Layout} (p : Path d) {a b : Layout} (h : At p = .struct a b) :
    At (rightPath p h) = b := by
  have hA := At_append p (cast (congrArg Path h.symm) (.right (.here : Path b)))
  have hB := At_cast h.symm (.right (.here : Path b))
  simp only [rightPath, hA, hB]

/-- A spine's head path ends at the array's element layout. -/
theorem headPath_at {d : Layout} (p : Path d) (a : Layout) (h : At p = .arr a) (k : Nat) :
    At (headPath p a h k) = a := by
  have hA := At_append p (cast (congrArg Path h.symm) (.index k (.here : Path a)))
  have hB := At_cast h.symm (.index k (.here : Path a))
  simp only [headPath, hA, hB]

/-! ## The tree types and the handle context -/

/-- A tree type: an observation of a description, or a protected node. Neither is
the other, and a node type is never an observation. -/
inductive TreeTy (d : Layout) where
  /-- An observation of `o`. -/
  | obs (o : ObsDesc)
  /-- A protected node, the handle a name holds. -/
  | node (n : NodeTy d)

/-- The tree context lowered to the one-cell fragment's: an observation keeps its
description, and a handle becomes a `cell` name — which the fragment's
observation judgement refuses, so a node name is never an observation. -/
def obsEnv {d : Layout} (Γ : Var → Option (TreeTy d)) : TyEnv :=
  fun x => (Γ x).map (fun t => match t with | .obs o => Ty.obs o | .node _ => Ty.cell)

/-- The context with `x` bound to the tree type `t`, shadowing whatever `x`
held. -/
def extendTy {d : Layout} (Γ : Var → Option (TreeTy d)) (x : Var) (t : TreeTy d) :
    Var → Option (TreeTy d) :=
  fun z => if z = x then some t else Γ z

/-- The context with `x` removed: the handle `x` held is spent, and no rule about
it is derivable afterwards. -/
def removeTy {d : Layout} (Γ : Var → Option (TreeTy d)) (x : Var) :
    Var → Option (TreeTy d) :=
  fun z => if z = x then none else Γ z

/-- The context that binds no name at all: the base every configuration below is
built from, name by name. -/
def emptyCtx {d : Layout} : Var → Option (TreeTy d) := fun _ => none

/-- The extended context holds the bound name. -/
@[simp] theorem extendTy_self {d : Layout} (Γ : Var → Option (TreeTy d)) (x : Var)
    (t : TreeTy d) : extendTy Γ x t x = some t := by
  simp [extendTy]

/-- The extended context leaves every other name as the context had it. -/
theorem extendTy_of_ne {d : Layout} {Γ : Var → Option (TreeTy d)} {x z : Var} {t : TreeTy d}
    (h : z ≠ x) : extendTy Γ x t z = Γ z := by
  simp [extendTy, h]

/-- A name the extended context does not hold the context did not hold either. -/
theorem extendTy_none_imp {d : Layout} {Γ : Var → Option (TreeTy d)} {x z : Var}
    {t : TreeTy d} (h : extendTy Γ x t z = none) : Γ z = none := by
  by_cases hzx : z = x
  · rw [hzx, extendTy_self] at h
    exact absurd h (by simp)
  · rwa [extendTy_of_ne hzx] at h

/-- The removed context holds nothing at the removed name: the handle is spent. -/
@[simp] theorem removeTy_self {d : Layout} (Γ : Var → Option (TreeTy d)) (x : Var) :
    removeTy Γ x x = none := by
  simp [removeTy]

/-- The removed context leaves every other name as the context had it. -/
theorem removeTy_of_ne {d : Layout} {Γ : Var → Option (TreeTy d)} {x z : Var} (h : z ≠ x) :
    removeTy Γ x z = Γ z := by
  simp [removeTy, h]

/-- A name the removed context still holds is a name that was not removed. -/
theorem removeTy_eq_some {d : Layout} {Γ : Var → Option (TreeTy d)} {x z : Var} {t : TreeTy d}
    (h : removeTy Γ x z = some t) : Γ z = some t := by
  by_cases hzx : z = x
  · rw [hzx, removeTy_self] at h
    exact absurd h (by simp)
  · rwa [removeTy_of_ne hzx] at h

/-- Neither tree type is an observation of a description, so a node-typed name is
never read as an observation. -/
theorem treeTy_node_ne_obs {d : Layout} {n : NodeTy d} {o : ObsDesc} :
    (TreeTy.node n : TreeTy d) ≠ .obs o := by
  intro h
  cases h

/-! ## The invariants of the context

Two standing conditions, each an index of every rule of the discipline: the
handles are one per path, and every handle a context can hold is one of a finite
list of paths. -/

/-- A handle context is well formed when one protected path has one live name: two
names that hold nodes at one path are one name. -/
def HandleWF {d : Layout} (Γ : Var → Option (TreeTy d)) : Prop :=
  ∀ x y n m, Γ x = some (.node n) → Γ y = some (.node m) → n.path = m.path → x = y

/-- The paths a context can bind: every live node of it is at one of them. The
list is what makes a fresh path a finite, decidable fact about a concrete
configuration. -/
def BindsPaths {d : Layout} (Γ : Var → Option (TreeTy d)) (S : List (Path d)) : Prop :=
  ∀ z n, Γ z = some (.node n) → n.path ∈ S

/-- The empty context binds no path. -/
theorem bindsPaths_empty {d : Layout} :
    BindsPaths (emptyCtx : Var → Option (TreeTy d)) [] := by
  intro z n hz
  simp [emptyCtx] at hz

/-- Binding a node adds its path to the paths a context binds. -/
theorem BindsPaths.extendTy_node {d : Layout} {Γ : Var → Option (TreeTy d)}
    {S : List (Path d)} {y : Var} {n : NodeTy d} (h : BindsPaths Γ S) :
    BindsPaths (extendTy Γ y (.node n)) (n.path :: S) := by
  intro z m hz
  by_cases hzy : z = y
  · rw [hzy, extendTy_self] at hz
    have hm : m = n := TreeTy.node.inj (Option.some.inj hz).symm
    subst hm
    simp
  · rw [extendTy_of_ne hzy] at hz
    exact List.mem_cons_of_mem _ (h z m hz)

/-- Binding an observation adds no path. -/
theorem BindsPaths.extendTy_obs {d : Layout} {Γ : Var → Option (TreeTy d)}
    {S : List (Path d)} {y : Var} {o : ObsDesc} (h : BindsPaths Γ S) :
    BindsPaths (extendTy Γ y (.obs o)) S := by
  intro z n hz
  by_cases hzy : z = y
  · rw [hzy, extendTy_self] at hz
    exact absurd hz (by simp)
  · rw [extendTy_of_ne hzy] at hz
    exact h z n hz

/-- Removing a name removes no path from those a context binds. -/
theorem BindsPaths.removeTy {d : Layout} {Γ : Var → Option (TreeTy d)} {S : List (Path d)}
    {x : Var} (h : BindsPaths Γ S) : BindsPaths (removeTy Γ x) S :=
  fun z n hz => h z n (removeTy_eq_some hz)

/-- A live name of a context that binds a path list not containing a node's path is
not that node: the freshness a binding rule needs. -/
theorem BindsPaths.free {d : Layout} {Γ : Var → Option (TreeTy d)} {S : List (Path d)}
    {n : NodeTy d} (h : BindsPaths Γ S) (hS : n.path ∉ S) :
    ∀ z m, Γ z = some (.node m) → n.path ≠ m.path :=
  fun z m hz hp => hS (hp ▸ h z m hz)

/-- The empty context is well formed: nothing is live at all. -/
theorem HandleWF.empty {d : Layout} : HandleWF (emptyCtx : Var → Option (TreeTy d)) := by
  intro x y n m hx
  simp [emptyCtx] at hx

/-- Binding an observation keeps a context well formed: an observation holds no
path. -/
theorem HandleWF.extendTy_obs {d : Layout} {Γ : Var → Option (TreeTy d)} {y : Var}
    {o : ObsDesc} (h : HandleWF Γ) : HandleWF (extendTy Γ y (.obs o)) := by
  intro x x' m m' hx hx' hp
  refine h x x' m m' ?_ ?_ hp
  · by_cases hxy : x = y
    · rw [hxy, extendTy_self] at hx
      exact absurd hx (by simp)
    · rwa [extendTy_of_ne hxy] at hx
  · by_cases hx'y : x' = y
    · rw [hx'y, extendTy_self] at hx'
      exact absurd hx' (by simp)
    · rwa [extendTy_of_ne hx'y] at hx'

/-- Binding a node at a path no live name holds keeps a context well formed: the
fresh name is the node's only live one. -/
theorem HandleWF.extendTy_node {d : Layout} {Γ : Var → Option (TreeTy d)} {y : Var}
    {n : NodeTy d} (h : HandleWF Γ)
    (hfree : ∀ z m, Γ z = some (.node m) → n.path ≠ m.path) :
    HandleWF (extendTy Γ y (.node n)) := by
  intro x x' m m' hx hx' hp
  by_cases hxy : x = y
  · rw [hxy, extendTy_self] at hx
    have hm : m = n := TreeTy.node.inj (Option.some.inj hx).symm
    subst hm
    by_cases hx'y : x' = y
    · exact hxy.trans hx'y.symm
    · rw [extendTy_of_ne hx'y] at hx'
      exact absurd hp (hfree x' m' hx')
  · rw [extendTy_of_ne hxy] at hx
    by_cases hx'y : x' = y
    · rw [hx'y, extendTy_self] at hx'
      have hm : m' = n := TreeTy.node.inj (Option.some.inj hx').symm
      subst hm
      exact absurd hp.symm (hfree x m hx)
    · rw [extendTy_of_ne hx'y] at hx'
      exact h x x' m m' hx hx' hp

/-- Removing a name keeps a context well formed. -/
theorem handleWF_removeTy {d : Layout} {Γ : Var → Option (TreeTy d)} {x : Var}
    (h : HandleWF Γ) : HandleWF (removeTy Γ x) :=
  fun a b n m ha hb hp => h a b n m (removeTy_eq_some ha) (removeTy_eq_some hb) hp

/-- The hand-off's context is well formed: removing the name the write went
through leaves the node's path to the one fresh name, because the removed name was
the subtree's only live one. -/
theorem HandleWF.handoff {d : Layout} {Γ : Var → Option (TreeTy d)} {x y : Var}
    {n : NodeTy d} (h : HandleWF Γ) (hx : Γ x = some (.node n)) :
    HandleWF (extendTy (removeTy Γ x) y (.node n)) := by
  have hrem : HandleWF (removeTy Γ x) := handleWF_removeTy h
  refine HandleWF.extendTy_node hrem ?_
  intro z m hz
  have hz' : Γ z = some (.node m) := removeTy_eq_some hz
  intro hp
  have hzx : z = x := h z x m n hz' hx hp.symm
  rw [hzx, removeTy_self] at hz
  exact absurd hz (by simp)

/-! ## The account's rights -/

/-- The account admits a write by the holder `w` at a node: the holder has the
whole of every node of the target's subtree, and a positive share of every proper
ancestor of the target. The two are read at the same nodes by construction — one
`Writes` per node of the subtree, one positive `Reads` per proper ancestor — so
nothing is inferred from a fraction somewhere else. -/
def WriteHolds {d : Layout} (A : Account d) (w : Nat) (p : Path d) : Prop :=
  (∀ q, InSubtree p q → Writes A q) ∧ (∀ r, PrefixOf r p → r ≠ p → ∃ q, 0 < q ∧ Reads A r w q)

/-! ## The state's replacement -/

/-- Replace the node a path addresses with a new state of the path's own layout:
a struct is rebuilt from its updated component, and an array element is taken out
of its slot with the default state left behind, handed back, replaced, and put
back — the take-out and put-back discipline the library's own nested update uses,
and no raw focus leaves this function. An index the state does not have answers
`none` rather than a state the replacement did not touch. -/
def replaceAt : (d : Layout) → (p : Path d) → State (At p) → State d → Option (State d)
  | _, .here, y, _ => some y
  | .struct a _, .left q, y, (u, v) => (replaceAt a q y u).map (fun u' => (u', v))
  | .struct _ b, .right q, y, (u, v) => (replaceAt b q y v).map (fun u' => (u, u'))
  | .arr a, .index i q, y, s =>
      if h : i < s.size then
        (replaceAt a q y s[i]).map (fun e' => s.set i e' h)
      else none

/-- The replacement's array case, level by level: at an in-bounds index the element
is taken out of its slot with the layout's default left behind, the replacement runs
on the extracted element, and the result is put back at that slot. -/
theorem replaceAt_index {a : Layout} (i : Nat) (q : Path a) (y : State (At q))
    (s : Array (State a)) (h : i < s.size) :
    replaceAt (.arr a) (.index i q) y s = (replaceAt a q y s[i]).map (fun e' => s.set i e' h) := by
  show (if h' : i < s.size then (replaceAt a q y s[i]).map (fun e' => s.set i e' h') else none)
    = (replaceAt a q y s[i]).map (fun e' => s.set i e' h)
  split
  · rfl
  · rename_i hlt
    exact absurd h hlt

/-- A replacement at an index the state does not have answers `none`: the rule's
own success premise is what refuses it. -/
theorem replaceAt_index_none {a : Layout} (i : Nat) (q : Path a) (y : State (At q))
    (s : Array (State a)) (h : ¬ i < s.size) :
    replaceAt (.arr a) (.index i q) y s = none := by
  rw [replaceAt]
  split
  · rename_i hlt
    exact absurd hlt h
  · rfl

/-- A replacement that answers `some` is at an in-bounds path: the rule's own
success premise therefore carries the bounds of every index on the path. -/
theorem replaceAt_inBounds {d : Layout} : ∀ (p : Path d) (y : State (At p)) (s : State d)
    {s' : State d}, replaceAt d p y s = some s' → InBounds p s := by
  intro p
  induction p with
  | here => intro y s s' _; trivial
  | left q ih =>
      intro y s s' h
      obtain ⟨u, v⟩ := s
      rw [replaceAt] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨u', hu', _⟩ := h
      exact ih y u hu'
  | right q ih =>
      intro y s s' h
      obtain ⟨u, v⟩ := s
      rw [replaceAt] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨u', hu', _⟩ := h
      exact ih y v hu'
  | index i q ih =>
      intro y s s' h
      rw [replaceAt] at h
      split at h
      · rename_i hlt
        rw [Option.map_eq_some_iff] at h
        obtain ⟨e', he', _⟩ := h
        exact ⟨s[i], Array.getElem?_eq_some_iff.mpr ⟨hlt, rfl⟩, ih y s[i] he'⟩
      · exact absurd h (by simp)

/-- Replace the node a path addresses by the struct node at `p` whose left
component is `u` and whose right component is the one the state has there: the
state the write rule installs, and `none` where the path addresses no node. -/
def setStructLeft {d : Layout} (p : Path d) {a b : Layout} (h : At p = .struct a b)
    (u : State a) (s : State d) : Option (State d) :=
  replaceAt d p (cast (congrArg State h.symm) (u, (cast (congrArg State h) (subAt p s)).2)) s

/-! ## The node quotations

A *recipe* is the freshly built node quotation a subtree replacement installs:
the term's instance is the node value of a state of that layout, so it names no
state the client holds and no focus of the interpreter's. -/

mutual

/-- A node quotation of a layout: the term `b`'s instance under `ρ` is the node
value of the state `u`. -/
inductive Recipe {d : Layout} (Γ : Var → Option (TreeTy d)) (ρ : VEnv) :
    (a : Layout) → Expr → State a → Prop where
  /-- A leaf: the unary root node of an observation of the leaf's description. -/
  | leaf {o : ObsDesc} {b : Expr} {xel : ObsEl o} (h : Obs (obsEnv Γ) b o)
      (hden : inst ρ b = quoteEl o xel) : Recipe Γ ρ (.leaf o) (.con1 rootTag b) xel
  /-- A struct: the binary struct node of its components' quotations. -/
  | struct {a b : Layout} {x y : Expr} {u : State a} {v : State b}
      (hx : Recipe Γ ρ a x u) (hy : Recipe Γ ρ b y v) :
      Recipe Γ ρ (.struct a b) (.con2 structTag x y) (u, v)
  /-- An array: the `nil`/`cons` spine of its elements' quotations. -/
  | arr {a : Layout} {b : Expr} {l : List (State a)}
      (h : RecipeList Γ ρ a b l) : Recipe Γ ρ (.arr a) b l.toArray

/-- A list of node quotations: the term's instance under `ρ` is the `nil`/`cons`
spine of the states' node values. -/
inductive RecipeList {d : Layout} (Γ : Var → Option (TreeTy d)) (ρ : VEnv) :
    (a : Layout) → Expr → List (State a) → Prop where
  /-- The empty spine. -/
  | nil : RecipeList Γ ρ a (.con0 nilTag) []
  /-- A head element and the rest of the spine. -/
  | cons {b t : Expr} {u : State a} {l : List (State a)}
      (h : Recipe Γ ρ a b u) (ht : RecipeList Γ ρ a t l) :
      RecipeList Γ ρ a (.con2 consTag b t) (u :: l)

end

/-! ## The judgement -/

/-- The tree ownership discipline: from the state `s`, the term `e` is admitted at
the tree type `τ`, holding the value `v`, and leaves the state `s'`, in the handle
context `Γ`, under the observation environment `ρ` and the per-node account `A`.
Each rule names the value it produces and the state it leaves, so an admitted
write carries its own success, and no rule is a catch-all. Every rule carries the
account's validity and the context's one-handle-per-path condition, so no
derivation exists without them. -/
inductive TreeOwn : (d : Layout) → (Γ : Var → Option (TreeTy d)) → (ρ : VEnv) →
    (A : Account d) → State d → Expr → TreeTy d → Expr → State d → Prop where
  /-- An observation is admitted at the unchanged configuration, holding its
  instance. -/
  | obs {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv} {A : Account d}
      {s : State d} {e : Expr} {o : ObsDesc} (h : Obs (obsEnv Γ) e o)
      (hA : ValidAccount A) (hΓ : HandleWF Γ) :
      TreeOwn d Γ ρ A s e (.obs o) (inst ρ e) s
  /-- A read of a leaf node, under the reader's own borrow there: the continuation's
  bound name holds the detached quotation of what was read. -/
  | read {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv} {A : Account d}
      {s : State d} (x y : Var) (body : Expr) {w : Nat} {p : Path d} {o : ObsDesc}
      {h : At p = .leaf o} (share : Path d → Rat) {v : Expr} {xel : ObsEl o}
      {τ : TreeTy d} {v' : Expr} {s' : State d}
      (hA : ValidAccount A) (hΓ : HandleWF Γ)
      (hx : Γ x = some (.node (.at w p (.leaf o) h)))
      (hval : ρ x = some (.con1 rootTag v))
      (hden : v = quoteEl o xel)
      (hloan : ReadLoan A w ⟨p, o, h⟩ share)
      (hread : read? ⟨p, o, h⟩ s = some (encodeObs o xel))
      (hy : Γ y = none) (hρy : ρ y = none)
      (hbody : TreeOwn d (extendTy Γ y (.obs o)) (VEnv.extend ρ y v) A s body τ v' s') :
      TreeOwn d Γ ρ A s (.matchC (.var x) rootTag [y] body) τ v' s'
  /-- A write of a leaf observation at the leaf node a name holds, under the
  account's write right there. The state left is the library's own leaf write,
  and it reports success. -/
  | write {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv} {A : Account d}
      {s : State d} (x : Var) (a : Expr) {w : Nat} {p : Path d} {o : ObsDesc}
      {h : At p = .leaf o} {v : Expr} {xel : ObsEl o} {s' : State d}
      (hA : ValidAccount A) (hΓ : HandleWF Γ)
      (hx : Γ x = some (.node (.at w p (.leaf o) h)))
      (hval : ρ x = some (.con1 rootTag v))
      (hobs : Obs (obsEnv Γ) a o)
      (hden : inst ρ a = quoteEl o xel)
      (hacc : WriteHolds A w p)
      (hwrite : setLeaf ⟨p, o, h⟩ xel s = (s', true)) :
      TreeOwn d Γ ρ A s (.store (.var x) 0 a) (.node (.at w p (.leaf o) h))
        (.con1 rootTag (inst ρ a)) s'
  /-- A subtree replacement at a struct node: the operand's instance is a freshly
  built node quotation of the node's left component, and the state left is the
  struct's own cell with that component replaced — the replacement's own `some`;
  an index the state does not have answers `none` and admits nothing. -/
  | writeSub {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv} {A : Account d}
      {s : State d} (x : Var) (b : Expr) {w : Nat} {p : Path d} {a c : Layout}
      {h : At p = .struct a c} {u : State a} {v₁ : Expr} {v₂ : Expr} {s' : State d}
      (hA : ValidAccount A) (hΓ : HandleWF Γ)
      (hx : Γ x = some (.node (.at w p (.struct a c) h)))
      (hval : ρ x = some (.con2 structTag v₁ v₂))
      (hrec : Recipe Γ ρ a b u)
      (hacc : WriteHolds A w p)
      (hwrite : setStructLeft p h u s = some s') :
      TreeOwn d Γ ρ A s (.store (.var x) 0 b) (.node (.at w p (.struct a c) h))
        (.con2 structTag (inst ρ b) v₂) s'
  /-- A descent into a struct node's two components, each under the node's own
  holder and each handed its own field value. -/
  | descendStruct {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv} {A : Account d}
      {s : State d} (x y z : Var) (body : Expr) {w : Nat} {p : Path d} {a c : Layout}
      {h : At p = .struct a c} {v₁ : Expr} {v₂ : Expr} {τ : TreeTy d} {v' : Expr}
      {s' : State d}
      (hA : ValidAccount A) (hΓ : HandleWF Γ)
      (hx : Γ x = some (.node (.at w p (.struct a c) h)))
      (hval : ρ x = some (.con2 structTag v₁ v₂))
      (hy : Γ y = none) (hρy : ρ y = none) (hz : Γ z = none) (hρz : ρ z = none)
      (hyz : y ≠ z)
      (hbody : TreeOwn d
          (extendTy (extendTy Γ y (.node (.at w (leftPath p h) a (leftPath_at p h)))) z
            (.node (.at w (rightPath p h) c (rightPath_at p h))))
          (VEnv.extend (VEnv.extend ρ y v₁) z v₂) A s body τ v' s') :
      TreeOwn d Γ ρ A s (.matchC (.var x) structTag [y, z] body) τ v' s'
  /-- A descent along an array spine: the head element's node and the rest of the
  spine, each under the spine's holder and each handed its own value. -/
  | descendSpine {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv} {A : Account d}
      {s : State d} (x y z : Var) (body : Expr) {w : Nat} {p : Path d} {a : Layout}
      {h : At p = .arr a} {k : Nat} {v₁ : Expr} {v₂ : Expr} {τ : TreeTy d} {v' : Expr}
      {s' : State d}
      (hA : ValidAccount A) (hΓ : HandleWF Γ)
      (hx : Γ x = some (.node (.spine w p a h k)))
      (hval : ρ x = some (.con2 consTag v₁ v₂))
      (hy : Γ y = none) (hρy : ρ y = none) (hz : Γ z = none) (hρz : ρ z = none)
      (hyz : y ≠ z)
      (hbody : TreeOwn d
          (extendTy (extendTy Γ y (.node (.at w (headPath p a h k) a (headPath_at p a h k)))) z
            (.node (.spine w p a h (k + 1))))
          (VEnv.extend (VEnv.extend ρ y v₁) z v₂) A s body τ v' s') :
      TreeOwn d Γ ρ A s (.matchC (.var x) consTag [y, z] body) τ v' s'
  /-- The hand-off: a write through the name `x` bound to a fresh name `y`. The
  continuation's context is the one of `x` with `x` removed — the handle `x` held
  is spent — and its fresh name holds the write's own node and value. -/
  | handoff {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv} {A : Account d}
      {s s₁ s₂ : State d} (x y : Var) (a e₂ : Expr) {n : NodeTy d} {τ : TreeTy d}
      {v₁ v₂ : Expr}
      (hA : ValidAccount A) (hΓ : HandleWF Γ)
      (hx : Γ x = some (.node n))
      (h₁ : TreeOwn d Γ ρ A s (.store (.var x) 0 a) (.node n) v₁ s₁)
      (hy : Γ y = none) (hρy : ρ y = none)
      (h₂ : TreeOwn d (extendTy (removeTy Γ x) y (.node n)) (VEnv.extend ρ y v₁) A s₁
        e₂ τ v₂ s₂) :
      TreeOwn d Γ ρ A s (.bind y (.store (.var x) 0 a) e₂) τ v₂ s₂
  /-- An observation binding: the continuation runs with the bound name holding
  the observation's value, at the unchanged holder and account. -/
  | obsBind {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv} {A : Account d}
      {s s₁ s₂ : State d} (y : Var) (e₁ e₂ : Expr) {o o' : ObsDesc} {v₁ v₂ : Expr}
      (hA : ValidAccount A) (hΓ : HandleWF Γ)
      (h₁ : TreeOwn d Γ ρ A s e₁ (.obs o) v₁ s₁)
      (hy : Γ y = none) (hρy : ρ y = none)
      (h₂ : TreeOwn d (extendTy Γ y (.obs o)) (VEnv.extend ρ y v₁) A s₁ e₂ (.obs o') v₂ s₂) :
      TreeOwn d Γ ρ A s (.bind y e₁ e₂) (.obs o') v₂ s₂

/-! ## The invariants an admitted derivation carries -/

/-- Every admitted derivation's account is valid: the per-node conservation
discipline is an index of the rules, so an overfull account admits nothing. -/
theorem treeOwn_validAccount : ∀ {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv}
    {A : Account d} {s : State d} {e : Expr} {τ : TreeTy d} {v : Expr} {s' : State d},
    TreeOwn d Γ ρ A s e τ v s' → ValidAccount A := by
  intro d₀ Γ₀ ρ₀ A₀ s₀ e₀ τ₀ v₀ s₀' h
  cases h <;> assumption

/-- Every admitted derivation's handle context holds one live handle per protected
path: two names for one subtree are not derivable. -/
theorem treeOwn_handleWF : ∀ {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv}
    {A : Account d} {s : State d} {e : Expr} {τ : TreeTy d} {v : Expr} {s' : State d},
    TreeOwn d Γ ρ A s e τ v s' → HandleWF Γ := by
  intro d₀ Γ₀ ρ₀ A₀ s₀ e₀ τ₀ v₀ s₀' h
  cases h <;> assumption

/-- A write an admitted term performs goes through a live handle, and that handle
is the path's only live one: the second name that would carry a second write of
the same subtree does not exist. -/
theorem treeOwn_store_handle {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv}
    {A : Account d} {s : State d} {x : Var} {a : Expr} {τ : TreeTy d} {v : Expr}
    {s' : State d} (h : TreeOwn d Γ ρ A s (.store (.var x) 0 a) τ v s') :
    ∃ n : NodeTy d, Γ x = some (.node n)
      ∧ ∀ y m, Γ y = some (.node m) → m.path = n.path → y = x := by
  cases h with
  | obs hobs => cases hobs
  | write x' a' hA hΓ hx hval hobs hden hacc hwrite =>
      refine ⟨_, hx, ?_⟩
      intro y m hy hp
      exact (hΓ x y _ m hx hy hp.symm).symm
  | writeSub x' b' hA hΓ hx hval hrec hacc hwrite =>
      refine ⟨_, hx, ?_⟩
      intro y m hy hp
      exact (hΓ x y _ m hx hy hp.symm).symm

/-! ## The account's refusal, and the write the rules cannot accept

The account's write right is a `Writes` at every node of the target's subtree, and
`spine_writer_excludes` turns that into a refutation as soon as any other holder
has a loan anywhere in that subtree. The refusal below is read at the same node
the right is claimed at. -/

/-- A node a holder owns whole has no reader: `spine_writer_excludes` read at the
target's own subtree. -/
theorem writeHolds_no_read {d : Layout} {A : Account d} {w : Nat} {p q : Path d}
    (h : WriteHolds A w p) (hq : InSubtree p q) {i : Nat} {r : Rat} (hr : Reads A q i r) :
    False :=
  spine_writer_excludes h.1 hq hr

/-- A write is never admitted as an observation: no rule gives a store an
observation type. -/
theorem tree_store_not_obs {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv}
    {A : Account d} {s : State d} {x : Var} {a : Expr} {o : ObsDesc} {v : Expr}
    {s' : State d} : ¬ TreeOwn d Γ ρ A s (.store (.var x) 0 a) (.obs o) v s' := by
  intro h
  cases h with
  | obs hobs => cases hobs

/-! ## The witness configurations

The two-leaf witness of `Scidonia.RC.TreeOwnership.Spine`: a struct of two naturals
whose left leaf the reader holds half of and whose right leaf the writer owns
whole, under a root whose two halves the two of them hold. A write at that root
reaches the node the reader holds; a write at the right leaf does not.
-/

/-- The name holding the witness's root. -/
def rootName : Var := 10

/-- The name holding the witness's left leaf. -/
def leftName : Var := 11

/-- The name holding the witness's right leaf. -/
def rightName : Var := 12

/-- The name a read's continuation binds. -/
def outName : Var := 13

/-- The witness's state: the left leaf holds 7 and the right leaf 9. -/
def witnessState : State siblingLayout := (7, 9)

/-- The handle at the witness's root: the struct node there, held by the writer. -/
def witnessRootTy : NodeTy siblingLayout := .at writerId siblingRoot siblingLayout rfl

/-- The handle at the witness's left leaf, held by the reader. -/
def witnessLeftTy : NodeTy siblingLayout := .at readerId siblingLeft (.leaf .nat) rfl

/-- The handle at the witness's right leaf, held by the writer. -/
def witnessRightTy : NodeTy siblingLayout := .at writerId siblingRight (.leaf .nat) rfl

/-- The witness's context with its root bound: one live name at the common root. -/
def witnessRootCtx : Var → Option (TreeTy siblingLayout) :=
  extendTy (emptyCtx : Var → Option (TreeTy siblingLayout)) rootName (.node witnessRootTy)

/-- The witness's context with its root and its left leaf bound. -/
def witnessLeftCtx : Var → Option (TreeTy siblingLayout) :=
  extendTy witnessRootCtx leftName (.node witnessLeftTy)

/-- The witness's context: its three nodes, each under its own holder. -/
def witnessCtx : Var → Option (TreeTy siblingLayout) :=
  extendTy witnessLeftCtx rightName (.node witnessRightTy)

/-- The paths the witness's root context can bind. -/
theorem witnessRootCtx_binds : BindsPaths witnessRootCtx [siblingRoot] :=
  bindsPaths_empty.extendTy_node

/-- The paths the witness's left context can bind. -/
theorem witnessLeftCtx_binds : BindsPaths witnessLeftCtx [siblingLeft, siblingRoot] :=
  witnessRootCtx_binds.extendTy_node

/-- The paths the witness's context can bind. -/
theorem witnessCtx_binds : BindsPaths witnessCtx [siblingRight, siblingLeft, siblingRoot] :=
  witnessLeftCtx_binds.extendTy_node

/-- The witness's root context holds one live handle per path. -/
theorem witnessRootCtx_handleWF : HandleWF witnessRootCtx :=
  (HandleWF.empty (d := siblingLayout)).extendTy_node (by
    intro z m hz
    have hm := bindsPaths_empty z m hz
    simp at hm)

/-- The witness's left context holds one live handle per path. -/
theorem witnessLeftCtx_handleWF : HandleWF witnessLeftCtx :=
  witnessRootCtx_handleWF.extendTy_node (by
    intro z m hz
    have hm := witnessRootCtx_binds z m hz
    simp at hm
    rw [hm]
    decide)

/-- The witness's context holds one live handle per path. -/
theorem witnessCtx_handleWF : HandleWF witnessCtx :=
  witnessLeftCtx_handleWF.extendTy_node (by
    intro z m hz
    have hm := witnessLeftCtx_binds z m hz
    simp at hm
    rcases hm with hm | hm
    · rw [hm]; decide
    · rw [hm]; decide)

/-- The witness's environment: each leaf's name holds the unary root node of its
own observation, and the root's name holds the struct node of the two. -/
def witnessEnv : VEnv :=
  fun z => if z = rootName then some (.con2 structTag (.con1 rootTag (.con0 7))
      (.con1 rootTag (.con0 9)))
    else if z = leftName then some (.con1 rootTag (.con0 7))
    else if z = rightName then some (.con1 rootTag (.con0 9))
    else none

/-- The reader's identifier names the left leaf's handle. -/
theorem witness_ctx_left : witnessCtx leftName = some (.node witnessLeftTy) := by
  simp [witnessCtx, witnessLeftCtx, witnessRootCtx, emptyCtx, extendTy, rootName, leftName,
    rightName]

/-- The writer's identifier names the root's handle. -/
theorem witness_ctx_root : witnessCtx rootName = some (.node witnessRootTy) := by
  simp [witnessCtx, witnessLeftCtx, witnessRootCtx, emptyCtx, extendTy, rootName, leftName,
    rightName]

/-- The writer's identifier names the right leaf's handle. -/
theorem witness_ctx_right : witnessCtx rightName = some (.node witnessRightTy) := by
  simp [witnessCtx, witnessLeftCtx, witnessRootCtx, emptyCtx, extendTy, rootName, leftName,
    rightName]

/-- The left leaf's ledger is the reader's loan, so the left leaf is a node the
reader holds. -/
theorem witness_left_read : Reads siblingAccount siblingLeft readerId (1 / 2) := by
  simp [Reads, sibling_ledger_left, siblingLeftLedger]

/-- The right leaf is held whole by the writer, so the account admits a write
there. -/
theorem witness_right_writes : Writes siblingAccount siblingRight := sibling_ledger_right

/-- The left leaf's path is in the root's subtree: the component path the struct
descent takes. -/
theorem witness_left_in_root : InSubtree siblingRoot (leftPath siblingRoot rfl) :=
  ⟨_, rfl⟩

/-! ## A write at the root the account refuses

The root's subtree contains the left leaf, and the left leaf's ledger is the
reader's half: the write right at the root demands the whole of every one of those
nodes and the reader's loan is one of them. -/

/-- A write at the witness's root is not derivable: the account's write right
there would have to be the whole of the left leaf, which is the reader's. -/
theorem witness_subtree_write_refused (b : Expr) {v : Expr} {s' : State siblingLayout} :
    ¬ TreeOwn siblingLayout witnessCtx witnessEnv siblingAccount witnessState
        (.store (.var rootName) 0 b) (.node witnessRootTy) v s' := by
  intro h
  cases h with
  | writeSub x b' hA hΓ hx' hval hrec hacc hwrite =>
      exact writeHolds_no_read hacc witness_left_in_root witness_left_read

/-- The root's ledger is not empty: the reader's half and the writer's are lent
there. -/
theorem witness_root_ledger_has_loan : ¬ Writes siblingAccount siblingRoot := by
  intro h
  rw [Writes, sibling_ledger_root] at h
  simp [siblingRootLedger] at h

/-! ## The write beside it, which the account admits

The right leaf is disjoint from the reader's node and under the same borrowed
root: the writer owns the right leaf whole and holds the positive half of the root
that the reader does not. -/

/-- Appending the root step changes no path: the root step descends into
nothing. -/
theorem append_here_right : ∀ {d : Layout} (p : Path d), Path.append p (Path.here : Path (At p)) = p
  | _, .here => rfl
  | _, .left p => by rw [append_left, append_here_right p]
  | _, .right p => by rw [append_right, append_here_right p]
  | _, .index _ p => by rw [append_index, append_here_right p]

/-- The subtree of the witness's right leaf is the leaf itself: below a leaf path
the only step left is the root step. -/
theorem inSubtree_siblingRight {q : Path siblingLayout} (h : InSubtree siblingRight q) :
    q = siblingRight := by
  obtain ⟨r, hr⟩ := h
  have hr' : r = Path.here := by cases r with | here => rfl
  rw [hr', append_here_right] at hr
  exact hr

/-- The paths that prefix the witness's right leaf: its own path and the common
root. -/
theorem prefixOf_siblingRight {p : Path siblingLayout} (h : PrefixOf p siblingRight) :
    p = siblingRoot ∨ p = siblingRight := by
  obtain ⟨r, hr⟩ := h
  cases p with
  | here => exact Or.inl rfl
  | right q =>
      cases q with
      | here => exact Or.inr rfl
  | left q =>
      cases q with
      | here => exact False.elim (absurd hr (by simp [Path.append, siblingRight]))

/-- The paths that prefix the witness's left leaf: its own path and the common
root. -/
theorem prefixOf_siblingLeft {p : Path siblingLayout} (h : PrefixOf p siblingLeft) :
    p = siblingRoot ∨ p = siblingLeft := by
  obtain ⟨r, hr⟩ := h
  cases p with
  | here => exact Or.inl rfl
  | left q =>
      cases q with
      | here => exact Or.inr rfl
  | right q =>
      cases q with
      | here => exact False.elim (absurd hr (by simp [Path.append, siblingLeft]))

/-- The account admits a write at the witness's right leaf: the writer owns that
leaf whole and holds a positive half of the common root. -/
theorem witness_right_writeHolds : WriteHolds siblingAccount writerId siblingRight := by
  refine ⟨?_, ?_⟩
  · intro q hq
    have hq' : q = siblingRight := inSubtree_siblingRight hq
    subst hq'
    exact sibling_ledger_right
  · intro r hr hne
    rcases prefixOf_siblingRight hr with rfl | rfl
    · exact ⟨1 / 2, by grind, by simp [Reads, sibling_ledger_root, siblingRootLedger, writerId]⟩
    · exact absurd rfl hne

/-- The account admits a write at the witness's right leaf by the *root's* own
holder as well: the exclusion is read at the node, and the root's holder is the
name the session begins from. -/
theorem witness_right_writeHolds_root : WriteHolds siblingAccount readerId siblingRight := by
  refine ⟨?_, ?_⟩
  · intro q hq
    have hq' : q = siblingRight := inSubtree_siblingRight hq
    subst hq'
    exact sibling_ledger_right
  · intro r hr hne
    rcases prefixOf_siblingRight hr with rfl | rfl
    · exact ⟨1 / 2, by grind, by simp [Reads, sibling_ledger_root, siblingRootLedger, readerId]⟩
    · exact absurd rfl hne

/-- The reader's borrow at the witness's left leaf: its identifier is the reader's
own, and the loan is the reader's share of the root and of the leaf. -/
theorem witnessLoan_read :
    ReadLoan siblingAccount readerId ⟨siblingLeft, .nat, rfl⟩ (fun _ => 1 / 2) := by
  refine ⟨?_, ?_⟩
  · intro p _
    grind
  · intro p hp
    rcases prefixOf_siblingLeft hp with rfl | rfl
    · simp [Reads, sibling_ledger_root, siblingRootLedger, readerId]
    · simp [Reads, sibling_ledger_left, siblingLeftLedger, readerId]

/-- The witness's write at its right leaf is admitted, and it is admitted while the
reader holds half of the left leaf and half of the shared root: the exclusion is at
the same node and the sibling's write is not excluded. -/
theorem witness_sibling_write_admitted :
    TreeOwn siblingLayout witnessCtx witnessEnv siblingAccount witnessState
      (.store (.var rightName) 0 (.con0 9)) (.node witnessRightTy) (.con1 rootTag (.con0 9))
      (setLeaf ⟨siblingRight, .nat, rfl⟩ 9 witnessState).1 :=
  TreeOwn.write (x := rightName) (a := .con0 9) (w := writerId) (p := siblingRight)
    (o := .nat) (h := rfl) (v := .con0 9) (xel := 9) (hA := siblingAccount_valid)
    (hΓ := witnessCtx_handleWF)
    (by simp [witnessCtx, witnessLeftCtx, witnessRootCtx, emptyCtx, extendTy, rootName, leftName,
      rightName, witnessRightTy])
    (by simp [witnessEnv, rootName, leftName, rightName])
    (Obs.nat 9) rfl witness_right_writeHolds
    (by rfl)

/-! ## A second write through a spent handle

The hand-off removes the name the write was performed through, so a later rule
about that name has no handle to read. The sequential hand-off — the continuation
writing through the *fresh* name — is admitted. -/

/-- The one-node configuration: a single leaf held by one name. -/
def cellName : Var := 0

/-- The fresh name a write's result is handed to. -/
def nextName : Var := 21

/-- The name a two-name configuration adds beside the first. -/
def aliasName : Var := 22

/-- The handle at the one-node layout's root. -/
def cellTy : NodeTy (.leaf .nat) := .at 0 (.here : Path (.leaf .nat)) (.leaf .nat) rfl

/-- The one-node context: one name holds the root. -/
def cellCtx : Var → Option (TreeTy (.leaf .nat)) :=
  extendTy (emptyCtx : Var → Option (TreeTy (.leaf .nat))) cellName (.node cellTy)

/-- The one-node context holds one live handle per path. -/
theorem cellCtx_handleWF : HandleWF cellCtx :=
  (HandleWF.empty (d := .leaf .nat)).extendTy_node (by
    intro z m hz
    have hm := bindsPaths_empty z m hz
    simp at hm)

/-- The one-node environment: the name holds the root node of 7. -/
def cellEnv : VEnv := fun z => if z = cellName then some (.con1 rootTag (.con0 7)) else none

/-- The one-node account: nothing is lent at the root, so it is held whole. -/
def cellAccount : Account (.leaf .nat) := [(.here, [])]

/-- The one-node account is valid. -/
theorem cellAccount_valid : ValidAccount cellAccount := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [cellAccount, List.mem_cons, List.not_mem_nil, or_false] at he
    rw [he]
    exact ⟨by simp, by grind, by simp⟩
  · decide

/-- The one-node account admits a write at the root: the whole is held there and
the root has no proper ancestor to hold a share of. -/
theorem cell_write_admitted : WriteHolds cellAccount 0 (.here : Path (.leaf .nat)) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    have hq' : q = (Path.here : Path (.leaf .nat)) := by cases q with | here => rfl
    subst hq'
    simp [Writes, cellAccount, ledgerAt]
  · intro r hr hne
    exact absurd (by cases r with | here => rfl) hne

/-- A context with the hand-off's removed name still holds nothing at it. -/
theorem extendTy_removeTy_self {d : Layout} (Γ : Var → Option (TreeTy d)) (x y : Var)
    (t : TreeTy d) (hxy : x ≠ y) : extendTy (removeTy Γ x) y t x = none := by
  simp [extendTy, removeTy, hxy]

/-- A write through a name the hand-off removed is not derivable: the
continuation's context holds nothing at that name. -/
theorem tree_write_spent_refused {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv}
    {A : Account d} {s : State d} {x y : Var} {a : Expr} {n : NodeTy d} {τ : TreeTy d}
    {v : Expr} {s' : State d} (hxy : x ≠ y)
    (h : TreeOwn d (extendTy (removeTy Γ x) y (.node n)) ρ A s (.store (.var x) 0 a) τ v s') :
    False := by
  have hnone := extendTy_removeTy_self Γ x y (.node n) hxy
  cases h with
  | obs hobs => cases hobs
  | write x' a' hA hΓ hx' _ _ _ _ _ =>
      rw [hnone] at hx'
      exact absurd hx' (by simp)
  | writeSub x' b' hA hΓ hx' _ _ _ _ =>
      rw [hnone] at hx'
      exact absurd hx' (by simp)

/-- A write through the name a write already consumed is not derivable: the
hand-off removed its name from the continuation's context. -/
theorem cell_spent_write_refused (obs : Expr) {τ : TreeTy (.leaf .nat)} {v : Expr}
    {s' : State (.leaf .nat)} :
    ¬ TreeOwn (.leaf .nat) cellCtx cellEnv cellAccount 7
        (.bind nextName (.store (.var cellName) 0 obs) (.store (.var cellName) 0 obs)) τ v s' := by
  intro h
  cases h with
  | obs hobs => cases hobs
  | obsBind y e₁ e₂ hA hΓ h₁ _ _ _ => exact tree_store_not_obs h₁
  | handoff x y a e₂ hA hΓ hx h₁ _ _ h₂ =>
      exact tree_write_spent_refused (by simp [cellName, nextName]) h₂

/-- The sequential hand-off is admitted: the second write is performed through the
fresh name the first write was handed to. -/
theorem cell_handoff_admitted :
    TreeOwn (.leaf .nat) cellCtx cellEnv cellAccount 7
      (.bind nextName (.store (.var cellName) 0 (.con0 5)) (.store (.var nextName) 0 (.con0 6)))
      (.node cellTy) (.con1 rootTag (.con0 6))
      (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 6
        (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 5 7).1).1 := by
  have h₁ : TreeOwn (.leaf .nat) cellCtx cellEnv cellAccount 7
      (.store (.var cellName) 0 (.con0 5)) (.node cellTy) (.con1 rootTag (.con0 5))
      (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 5 7).1 :=
    TreeOwn.write (x := cellName) (a := .con0 5) (w := 0)
      (p := (Path.here : Path (.leaf .nat))) (o := .nat) (h := rfl) (v := .con0 7) (xel := 5)
      (hA := cellAccount_valid) (hΓ := cellCtx_handleWF)
      (by simp [cellCtx, emptyCtx, extendTy, cellName, cellTy])
      (by simp [cellEnv, cellName])
      (Obs.nat 5) rfl cell_write_admitted (by rfl)
  have h₂ : TreeOwn (.leaf .nat) (extendTy (removeTy cellCtx cellName) nextName (.node cellTy))
      (VEnv.extend cellEnv nextName (.con1 rootTag (.con0 5))) cellAccount
      (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 5 7).1
      (.store (.var nextName) 0 (.con0 6)) (.node cellTy) (.con1 rootTag (.con0 6))
      (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 6
        (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 5 7).1).1 :=
    TreeOwn.write (x := nextName) (a := .con0 6) (w := 0)
      (p := (Path.here : Path (.leaf .nat))) (o := .nat) (h := rfl)
      (v := .con0 5) (xel := 6)
      (hA := cellAccount_valid)
      (hΓ := cellCtx_handleWF.handoff (by rw [cellCtx, extendTy_self]))
      (by rw [extendTy_self]; rfl)
      (by rw [VEnv.extend_self])
      (Obs.nat 6) rfl cell_write_admitted (by rfl)
  exact TreeOwn.handoff (x := cellName) (y := nextName) (a := .con0 5)
    (e₂ := .store (.var nextName) 0 (.con0 6)) (n := cellTy)
    (hA := cellAccount_valid) (hΓ := cellCtx_handleWF)
    (by simp [cellCtx, extendTy, cellName, cellTy]) h₁
    (by simp [cellCtx, emptyCtx, extendTy, cellName, nextName])
    (by simp [cellEnv, cellName, nextName, cellTy]) h₂

/-! ## The write handed two names of one subtree

Two names of one client for one protected node: the context that would carry the
second write holds the one node at two names, and no rule admits a context like
that. The two-name configuration, the write it would perform, and the admitted
sequential hand-off beside it are the refusal and its control. -/

/-- The two-name configuration: the one node held at two names. -/
def aliasCtx : Var → Option (TreeTy (.leaf .nat)) :=
  extendTy cellCtx aliasName (.node cellTy)

/-- The two-name configuration holds one node at two names, so it is not a
well-formed handle context: this is the alias the discipline refuses, and the
detector the refusal below is read with. -/
theorem aliasCtx_not_handleWF : ¬ HandleWF aliasCtx := by
  intro h
  have hx : aliasCtx cellName = some (.node cellTy) := by
    simp [aliasCtx, cellCtx, emptyCtx, extendTy, cellName, aliasName]
  have hy : aliasCtx aliasName = some (.node cellTy) := by
    simp [aliasCtx, cellCtx, emptyCtx, extendTy, cellName, aliasName]
  exact (by decide : cellName ≠ aliasName) (h cellName aliasName cellTy cellTy hx hy rfl)

/-- The write handed two names of one subtree is not derivable: the context that
would carry it holds the one node at two names, and every rule of the discipline
requires one live handle per path. -/
theorem cell_two_name_refused (obs obs' : Expr) {τ : TreeTy (.leaf .nat)} {v : Expr}
    {s' : State (.leaf .nat)} :
    ¬ TreeOwn (.leaf .nat) aliasCtx cellEnv cellAccount 7
        (.bind nextName (.store (.var cellName) 0 obs) (.store (.var aliasName) 0 obs')) τ v s' :=
  fun h => aliasCtx_not_handleWF (treeOwn_handleWF h)

/-- The same expression in the one-name configuration *is* admitted, and it is
admitted through the fresh name the hand-off installs: the refusal above is the
two names, not the shape of the program. -/
theorem cell_two_name_control : TreeOwn (.leaf .nat) cellCtx cellEnv cellAccount 7
    (.bind nextName (.store (.var cellName) 0 (.con0 5)) (.store (.var nextName) 0 (.con0 6)))
    (.node cellTy) (.con1 rootTag (.con0 6))
    (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 6
      (setLeaf ⟨(Path.here : Path (.leaf .nat)), .nat, rfl⟩ 5 7).1).1 :=
  cell_handoff_admitted

/-! ## A read at a node that is not a leaf

The read rule's node is carried by its handle and must be a leaf: a struct node's
handle is not one, so no read at it is derivable. The same expression shape at a
leaf's handle is the read the rules accept. -/

/-- A read at the witness's root is not derivable: its handle is a struct node and
the read rule's node ends at a leaf. -/
theorem witness_struct_read_refused (body : Expr) {v : Expr} {s' : State siblingLayout} :
    ¬ TreeOwn siblingLayout witnessCtx witnessEnv siblingAccount witnessState
        (.matchC (.var rootName) rootTag [outName] body) (.obs .nat) v s' := by
  intro h
  cases h with
  | obs hobs => cases hobs
  | read x y body' share hA hΓ hx' _ _ _ _ _ _ _ =>
      rw [witness_ctx_root] at hx'
      simp only [Option.some.injEq, TreeTy.node.injEq] at hx'
      cases congrArg NodeTy.layout hx'

/-- A read at the witness's left leaf is admitted: the borrow is the reader's and
the continuation is handed the detached quotation of the element read. It is a
read on the reader's side of the shared spine, while the write the same account
admits is on the writer's side. -/
theorem witness_leaf_read_admitted :
    TreeOwn siblingLayout witnessCtx witnessEnv siblingAccount witnessState
      (.matchC (.var leftName) rootTag [outName] (.var outName)) (.obs .nat) (.con0 7)
      witnessState :=
  TreeOwn.read (x := leftName) (y := outName) (body := .var outName) (w := readerId)
    (p := siblingLeft) (o := .nat) (h := rfl) (share := fun _ => 1 / 2)
    (v := .con0 7) (xel := 7) (hA := siblingAccount_valid) (hΓ := witnessCtx_handleWF)
    (by simp [witnessCtx, witnessLeftCtx, witnessRootCtx, emptyCtx, extendTy, rootName, leftName,
      rightName, witnessLeftTy])
    (by simp [witnessEnv, rootName, leftName, rightName])
    rfl witnessLoan_read
    (by rfl)
    (by simp [witnessCtx, witnessLeftCtx, witnessRootCtx, emptyCtx, extendTy, rootName, leftName,
      rightName, outName])
    (by simp [witnessEnv, rootName, leftName, rightName, outName])
    (TreeOwn.obs (Obs.var outName
      (by simp [obsEnv, extendTy, witnessCtx, witnessLeftCtx, witnessRootCtx, emptyCtx, rootName,
        leftName, rightName, outName])
      Fragment.nat) siblingAccount_valid
      (witnessCtx_handleWF.extendTy_obs))

/-! ## An out-of-bounds leaf write

The write rule's own success premise is what refuses a write whose index addresses
nothing: the library's `setLeaf` reports failure there. -/

/-- The one-element array layout. -/
def arrLayout : Layout := .arr (.leaf .nat)

/-- The array's state. -/
def arrState : State arrLayout := #[1, 2, 3]

/-- The one-element array's handle at its element 1. -/
def arrTy (i : Nat) : NodeTy arrLayout :=
  .at 0 (.index i (.here : Path (.leaf .nat))) (.leaf .nat) rfl

/-- The array's context: one name holds element 1 and one holds element 5. -/
def arrCtx : Var → Option (TreeTy arrLayout) :=
  extendTy (extendTy (emptyCtx : Var → Option (TreeTy arrLayout)) rootName (.node (arrTy 1)))
    leftName (.node (arrTy 5))

/-- The array's context holds one live handle per path. -/
theorem arrCtx_handleWF : HandleWF arrCtx := by
  have hb : BindsPaths (extendTy (emptyCtx : Var → Option (TreeTy arrLayout)) rootName
      (.node (arrTy 1))) [(arrTy 1).path] := bindsPaths_empty.extendTy_node
  refine ((HandleWF.empty (d := arrLayout)).extendTy_node ?_).extendTy_node ?_
  · intro z m hz
    have hm := bindsPaths_empty z m hz
    simp at hm
  · intro z m hz
    have hm := hb z m hz
    simp at hm
    rw [hm]
    decide

/-- The array's environment: each name holds the root node of the element it
names, when that element exists. -/
def arrEnv : VEnv :=
  fun z => if z = rootName then some (.con1 rootTag (.con0 2))
    else if z = leftName then some (.con1 rootTag (.con0 2))
    else none

/-- The array's account: the writer's half is lent at the root, and nothing at
either element. -/
def arrAccount : Account arrLayout := [(.here, [(0, 1 / 2)])]

/-- The array's account is valid: one half at the root, nothing at the elements. -/
theorem arrAccount_valid : ValidAccount arrAccount := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [arrAccount, List.mem_cons, List.not_mem_nil, or_false] at he
    rw [he]
    exact ⟨by intro x hx; rw [List.mem_singleton] at hx; rw [hx]; exact one_half_valid,
      by grind, by simp⟩
  · rw [arrAccount]
    decide

/-- The paths that prefix the array's element 1: the root and the element
itself. -/
theorem prefixOf_arrElement {p : Path arrLayout}
    (h : PrefixOf p (.index 1 (.here : Path (.leaf .nat)))) :
    p = Path.here ∨ p = .index 1 (.here : Path (.leaf .nat)) := by
  obtain ⟨r, hr⟩ := h
  cases p with
  | here => exact Or.inl rfl
  | index i q =>
      cases q with
      | here =>
          cases r with
          | here =>
              exact Or.inr (by cases hr; rfl)

/-- The account admits a write at element 1: the writer holds the element's whole
and holds a positive half of the array's own node. -/
theorem arr_write_admitted : WriteHolds arrAccount 0 (.index 1 (.here : Path (.leaf .nat))) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    obtain ⟨r, hr⟩ := hq
    subst hr
    show ledgerAt arrAccount (Path.index 1 r) = []
    have hne : (Path.index 1 r : Path arrLayout) ≠ Path.here := by
      intro h
      cases h
    have hne' : (Path.index 1 r : Path arrLayout) ≠ .index 5 (.here : Path (.leaf .nat)) := by
      intro h
      exact (by decide : (1 : Nat) ≠ 5) (Path.index.inj h).1
    simp only [arrAccount, ledgerAt, hne, hne', reduceIte]
    rfl
  · intro r hr hne
    rcases prefixOf_arrElement hr with rfl | rfl
    · exact ⟨1 / 2, by grind, by simp [Reads, arrAccount, ledgerAt, rootName]⟩
    · exact absurd rfl hne

/-- A leaf write's success report does not depend on the observation written:
`setLeaf` asks only whether the path addresses anything. -/
theorem setLeaf_snd_irrelevant {d : Layout} (p : ObsPath d) (x y : ObsEl p.obs) (s : State d) :
    (setLeaf p x s).2 = (setLeaf p y s).2 := by
  simp only [setLeaf]
  split <;> rfl

/-- A write whose index addresses nothing is not derivable: the rule's own
success premise is the library's failure report. -/
theorem arr_out_of_bounds_refused (obs : Expr) {v : Expr} {s' : State arrLayout} :
    ¬ TreeOwn arrLayout arrCtx arrEnv arrAccount arrState
        (.store (.var leftName) 0 obs) (.node (arrTy 5)) v s' := by
  intro h
  cases h with
  | write x a hA hΓ hx' _ _ _ _ hwrite' =>
      have h2 : ∃ xel : ObsEl .nat,
          (setLeaf ⟨(.index 5 (.here : Path (.leaf .nat))), (.nat : ObsDesc), rfl⟩ xel arrState).2
            = true :=
        ⟨_, congrArg Prod.snd hwrite'⟩
      rcases h2 with ⟨xel, hxel⟩
      have h3 : (setLeaf ⟨(.index 5 (.here : Path (.leaf .nat))), (.nat : ObsDesc), rfl⟩ xel
          arrState).2 = false := rfl
      rw [h3] at hxel
      exact absurd hxel (by simp)

/-- The in-bounds element of the same array is one the account admits a write
at. -/
theorem arr_in_bounds_admitted :
    WriteHolds arrAccount 0 (.index 1 (.here : Path (.leaf .nat))) :=
  arr_write_admitted

/-! ## An out-of-bounds subtree replacement

A nonleaf replacement descends through the array indices on its path. The library
replacement answers `some` only where every one of them addresses an element and
`none` where one does not, and the rule carries that answer as its own success
premise: a replacement at an index the state does not have admits nothing, beside
the in-bounds replacement of the same shape, which it does.
-/

/-- The array-of-structs layout: an array whose elements are pairs of
naturals. -/
def subLayout : Layout := .arr (.struct (.leaf .nat) (.leaf .nat))

/-- The element layout the array's struct nodes end at. -/
def subElem : Layout := .struct (.leaf .nat) (.leaf .nat)

/-- The array-of-structs state: the pairs the elements hold. -/
def subState : State subLayout := #[(1, 2), (3, 4)]

/-- The path to the struct node at the state's element 0. -/
def subPath : Path subLayout := .index 0 (.here : Path subElem)

/-- The path to a struct node at an element the state does not have. -/
def subMissing : Path subLayout := .index 5 (.here : Path subElem)

/-- The handle at the state's element 0. -/
def subTy : NodeTy subLayout := .at 0 subPath subElem rfl

/-- The handle at the element the state does not have. -/
def subMissingTy : NodeTy subLayout := .at 0 subMissing subElem rfl

/-- The array-of-structs context: one name at element 0 and one at the element the
state does not have. -/
def subCtx : Var → Option (TreeTy subLayout) :=
  extendTy (extendTy (emptyCtx : Var → Option (TreeTy subLayout)) rootName (.node subTy))
    leftName (.node subMissingTy)

/-- The array-of-structs context holds one live handle per path. -/
theorem subCtx_handleWF : HandleWF subCtx := by
  have hb : BindsPaths (extendTy (emptyCtx : Var → Option (TreeTy subLayout)) rootName
      (.node subTy)) [subPath] := bindsPaths_empty.extendTy_node
  refine ((HandleWF.empty (d := subLayout)).extendTy_node ?_).extendTy_node ?_
  · intro z m hz
    have hm := bindsPaths_empty z m hz
    simp at hm
  · intro z m hz
    have hm := hb z m hz
    simp only [List.mem_singleton] at hm
    rw [hm]
    simp only [NodeTy.path, subMissingTy, subTy]
    decide

/-- The array-of-structs environment: each name holds the struct node of the pair
its element holds. -/
def subEnv : VEnv :=
  fun z => if z = rootName then
      some (.con2 structTag (.con1 rootTag (.con0 1)) (.con1 rootTag (.con0 2)))
    else if z = leftName then
      some (.con2 structTag (.con1 rootTag (.con0 1)) (.con1 rootTag (.con0 2)))
    else none

/-- The array-of-structs account: the holder's half is lent at the array's node
and nothing is lent at either element's struct node. -/
def subAccount : Account subLayout := [(.here, [(0, 1 / 2)])]

/-- The array-of-structs account is valid. -/
theorem subAccount_valid : ValidAccount subAccount := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [subAccount, List.mem_cons, List.not_mem_nil, or_false] at he
    rw [he]
    exact ⟨by intro x hx; rw [List.mem_singleton] at hx; rw [hx]; exact one_half_valid,
      by grind, by simp⟩
  · rw [subAccount]
    decide

/-- The paths that prefix the array's element 5: the root and the element
itself. -/
theorem prefixOf_subMissing {p : Path subLayout} (h : PrefixOf p subMissing) :
    p = Path.here ∨ p = subMissing := by
  obtain ⟨r, hr⟩ := h
  cases p with
  | here => exact Or.inl rfl
  | index i q =>
      cases q with
      | here => exact Or.inr (by cases hr; rfl)
      | left q' => exact absurd hr (by cases hr)
      | right q' => exact absurd hr (by cases hr)

/-- The account admits a write at the element the state does not have: the whole
of the element's subtree and a positive half of the array's own node. -/
theorem sub_missing_writeHolds : WriteHolds subAccount 0 subMissing := by
  refine ⟨?_, ?_⟩
  · intro q hq
    obtain ⟨r, hr⟩ := hq
    subst hr
    show ledgerAt subAccount (Path.index 5 r) = []
    have hne : (Path.index 5 r : Path subLayout) ≠ Path.here := by
      intro h; cases h
    simp only [subAccount, ledgerAt, hne, reduceIte]
    rfl
  · intro r hr hne
    rcases prefixOf_subMissing hr with rfl | rfl
    · exact ⟨1 / 2, by grind, by simp [Reads, subAccount, ledgerAt, rootName]⟩
    · exact absurd rfl hne

/-- The paths that prefix the array's element 0: the root and the element
itself. -/
theorem prefixOf_subPath {p : Path subLayout} (h : PrefixOf p subPath) :
    p = Path.here ∨ p = subPath := by
  obtain ⟨r, hr⟩ := h
  cases p with
  | here => exact Or.inl rfl
  | index i q =>
      cases q with
      | here => exact Or.inr (by cases hr; rfl)
      | left q' => exact absurd hr (by cases hr)
      | right q' => exact absurd hr (by cases hr)

/-- The account admits a write at the element the state has: the whole of the
element's subtree and a positive half of the array's own node. -/
theorem sub_present_writeHolds : WriteHolds subAccount 0 subPath := by
  refine ⟨?_, ?_⟩
  · intro q hq
    obtain ⟨r, hr⟩ := hq
    subst hr
    show ledgerAt subAccount (Path.index 0 r) = []
    have hne : (Path.index 0 r : Path subLayout) ≠ Path.here := by
      intro h; cases h
    simp only [subAccount, ledgerAt, hne, reduceIte]
    rfl
  · intro r hr hne
    rcases prefixOf_subPath hr with rfl | rfl
    · exact ⟨1 / 2, by grind, by simp [Reads, subAccount, ledgerAt, rootName]⟩
    · exact absurd rfl hne

/-- A subtree replacement whose path descends through an index the state does not
have is not derivable: the replacement answers `none` there, and the rule's own
success premise therefore fails. -/
theorem sub_out_of_bounds_refused (b : Expr) {v : Expr} {s' : State subLayout} :
    ¬ TreeOwn subLayout subCtx subEnv subAccount subState
        (.store (.var leftName) 0 b) (.node subMissingTy) v s' := by
  intro h
  cases h with
  | writeSub x b' hA hΓ hx' hval hrec hacc hwrite =>
      unfold setStructLeft at hwrite
      have hb : InBounds subMissing subState := replaceAt_inBounds subMissing _ subState hwrite
      obtain ⟨e, he, _⟩ := hb
      simp only [subMissing, subState] at he
      exact absurd he (by simp)

/-- The in-bounds replacement of the same shape is admitted: the same expression
through element 0 is derivable, and the state it leaves is the array with that
element's struct node rebuilt. -/
theorem sub_in_bounds_admitted :
    ∃ s' : State subLayout,
      TreeOwn subLayout subCtx subEnv subAccount subState
        (.store (.var rootName) 0 (.con1 rootTag (.con0 5))) (.node subTy)
        (.con2 structTag (.con1 rootTag (.con0 5)) (.con1 rootTag (.con0 2))) s' :=
  ⟨_, TreeOwn.writeSub (x := rootName) (b := .con1 rootTag (.con0 5)) (w := 0)
    (p := subPath) (a := .leaf .nat) (c := .leaf .nat) (h := rfl) (u := 5)
    (v₁ := .con1 rootTag (.con0 1)) (v₂ := .con1 rootTag (.con0 2))
    (hA := subAccount_valid) (hΓ := subCtx_handleWF)
    (by
      show subCtx rootName = some (.node subTy)
      simp only [subCtx, subTy, subPath, subElem, rootName, leftName, emptyCtx, extendTy]
      rfl)
    (by
      show subEnv rootName = some (.con2 structTag (.con1 rootTag (.con0 1))
        (.con1 rootTag (.con0 2)))
      simp [subEnv, rootName, leftName])
    (Recipe.leaf (Obs.nat 5) rfl) sub_present_writeHolds
    (by
      simp only [setStructLeft, subPath, subLayout, subElem]
      rw [replaceAt_index (a := .struct (.leaf .nat) (.leaf .nat)) 0
        (Path.here : Path (.struct (.leaf .nat) (.leaf .nat))) _ subState (by decide)]
      rfl)⟩

end TreeOwnership

end Scidonia.RC
