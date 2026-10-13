/-
The executor of the tree fragment: the private interpreter, the session's
value-level evaluation, its `IO` runner, and the agreement and totality theorems
that relate them to the copying λPure reduction of `Scidonia.RC.Pure`.

**Two semantics of one term.** The *copying* side is the existing
`Scidonia.RC.Step`/`StepStar`/`Value` of `Scidonia.RC.Pure`, read at the instance
of the term — the term the interpreter's environment is instantiated into, and
not a second syntax. The *direct* side is `runTree`, a structurally recursive
interpreter of the admitted fragment that threads the layout's state, the handle
context of the judgement and an observation environment, and returns a λPure
value together with the state it leaves. `runTree_simulate` relates the two: for
an admitted term, with the handle function agreeing with the context, the
environment holding closed λPure values and the context's observation names
holding unrooted ones, the direct evaluation returns exactly the judgement's
value index, and the copying reduction of the term's instance reaches that value.

**The handle function.** The interpreter cannot read a handle off the context: a
`TreeTy` is a type, and the rules a read, a descent and a write go through name
their node by its *shape* — the path, the layout at the path's end and the
holder. The extra argument `hnd` carries that shape, and `HndAgrees Γ hnd` says
it is the context's own: a name the context holds at a node holds exactly that
node. `ClosedEnv` is the environment half — every value it holds is a closed
λPure value — and `ObsAgrees` is the observation half: a name the context holds
at an observation holds a value, and that value is *unrooted*. The last is not
implied by the other two: an environment may hold a protected node at a name the
context holds at an observation, and it is exactly that configuration the shape
component of the simulation's conclusion, `Shape`, rules out.

**The value indices.** A rule's value index is exactly the expression the
corresponding interpreter clause computes: an observation is the instance of the
term, a read is what its continuation produced, a write is the unary root node of
the written observation, a subtree replacement is the struct node of its operand's
instance and the component it did not touch, and a binding is what its
continuation produced. Each arm of the simulation is therefore the interpreter
clause reduced at the rule's hypotheses followed by the induction hypothesis at
the continuation, and its copying side is the rule's own redex — `Root.matchVal`
for a read or a descent, `Root.storeVal` for a write, `Root.bindVal` behind
`stepStar_bindFun` for a binding — composed with `subst_inst`, and with the
two-name form `subst_two_inst` for a descent, whose arm substitutes both of its
binders at once.

**The freshness of the bound names.** The substitution the reduction performs and
the interpreter's environment extension agree exactly when the name a rule binds
is one the environment does not hold, and that is the discipline the judgement
carries: every binder's name is absent from the environment at the point it
binds. Since an environment only ever *grows*, a name the environment holds is
never bound by any rule of the derivation (`treeOwn_binders_fresh`), and it is
that half of the freshness — not the context's — which the two-name substitution
of a descent rests on. A read's or an observation binding's name is held at an
observation, which no rule ever removes, and a hand-off's name is held at a node
the environment holds as well, so neither can be re-bound.

**The session.** The session's context holds one name, `sessionName`, at the root
*node* of the layout, and its environment holds that node's value — the quotation
of the state. A name at an observation is what a read's continuation or an
observation binding introduces, and the session configuration holds none, so the
observation agreement is discharged there vacuously.

**What is proved.** `evalTree_sound` is the agreement at the session: an admitted
program's evaluation returns a value the copying reduction of the program
reaches. `evalTree_sound_closed` is the same statement for a closed program, with
`inst_rootEnv_eq` turning the instance into the program itself. `evalTree_total`
is totality: every admitted program's evaluation returns a value the reduction
reaches. `evalTree_no_protected` reads the shape component off an
observation-typed program: no protected node — no handle, subtree or array — is
among the values the session returns. `runTreeIO` is the `IO` description over the
private interpreter, and `runTreeIO_of_evalTree` is its single `return`.
-/
import Scidonia.RC.TreeOwnership.Judgement
import Scidonia.RC.OwnershipTyped.Refinement

namespace Scidonia.RC

namespace TreeOwnership

open Scidonia.FracPerm.StateVar (Slot)
open Scidonia.FracPerm.StateVar.Layout5
open Scidonia.RC.OwnershipTyped (Ty Obs Denote Fragment VEnv inst subst_inst binders
  obs_binders_nil stepStar_bindFun rootTag unitTag emptyTag)

/-! ## The agreement predicates -/

/-- The handle context and the handle function agree: a name the context holds at
a node holds exactly that node. A name the context holds at an observation is
outside the agreement, because an observation's value is not a node. -/
def HndAgrees {d : Layout} (Γ : Var → Option (TreeTy d))
    (hnd : Var → Option (NodeTy d)) : Prop :=
  ∀ x n, Γ x = some (.node n) → hnd x = some n

/-- The environment holds λPure values, and they are closed: every name the
environment holds a value for holds one that mentions no variable. -/
def ClosedEnv (ρ : VEnv) : Prop := ∀ x w, ρ x = some w → Value w ∧ Closed w

/-- The environment agrees with the context's observation types: a name the
context holds at an observation holds a value, and that value carries no
protected node. The value's presence is part of the agreement because the
interpreter's variable clause is what an observation variable evaluates to, so a
name the environment does not hold is not evaluated at all. -/
def ObsAgrees {d : Layout} (Γ : Var → Option (TreeTy d)) (ρ : VEnv) : Prop :=
  ∀ x o, Γ x = some (.obs o) → ∃ w, ρ x = some w ∧ hasProtected w = false

/-- The shape a tree type gives its result: an observation carries no protected
node — no unary root node, no subtree and no array — and a handle carries
whatever its rule names. -/
def Shape {d : Layout} : TreeTy d → Expr → Prop
  | .obs _, v => hasProtected v = false
  | .node _, _ => True

/-! ## The handle function's extensions -/

/-- The handle function with `x` holding the node `n`, shadowing whatever `x`
held. -/
private def extendHnd {d : Layout} (hnd : Var → Option (NodeTy d)) (x : Var) (n : NodeTy d) :
    Var → Option (NodeTy d) :=
  fun z => if z = x then some n else hnd z

/-- The handle a bound term hands to its continuation's fresh name, when the
bound term is a write through a handle: the handle the write went through. Every
other bound term hands nothing on. -/
private def handedHnd? {d : Layout} (hnd : Var → Option (NodeTy d)) : Expr → Option (NodeTy d)
  | .store (.var x) 0 _ => hnd x
  | _ => none

/-- The handle function a binding's continuation runs with: the fresh name `y`
takes over the handle a write handed on, and every other bound term leaves the
handle function alone. -/
private def nextHnd {d : Layout} (hnd : Var → Option (NodeTy d)) (y : Var) (e₁ : Expr) :
    Var → Option (NodeTy d) :=
  match handedHnd? hnd e₁ with
  | some n => extendHnd hnd y n
  | none => hnd

/-- A handle function extended at a fresh name agrees with the context extended
with that name's node. -/
theorem HndAgrees.extendNode {d : Layout} {Γ : Var → Option (TreeTy d)}
    {hnd : Var → Option (NodeTy d)} {y : Var} {n : NodeTy d} (h : HndAgrees Γ hnd) :
    HndAgrees (extendTy Γ y (.node n)) (extendHnd hnd y n) := by
  intro z n' hz
  by_cases hzy : z = y
  · subst hzy
    rw [extendTy_self] at hz
    cases hz
    simp [extendHnd]
  · rw [extendTy_of_ne hzy] at hz
    simp only [extendHnd, ite_eq_right hzy]
    exact h z n' hz

/-- A handle function extended at a fresh name agrees with a context that holds
that name at an observation: the new name is not a node, so the agreement has
nothing to say about it. -/
theorem HndAgrees.extendObs {d : Layout} {Γ : Var → Option (TreeTy d)}
    {hnd : Var → Option (NodeTy d)} {y : Var} {o : ObsDesc} (h : HndAgrees Γ hnd) :
    HndAgrees (extendTy Γ y (.obs o)) hnd := by
  intro z n hz
  by_cases hzy : z = y
  · subst hzy
    rw [extendTy_self] at hz
    exact absurd hz (by simp)
  · rw [extendTy_of_ne hzy] at hz
    exact h z n hz

/-- A handle function agrees with the context the hand-off removes a name from:
the removed name is the only one the context changed at. -/
theorem HndAgrees.removeTy {d : Layout} {Γ : Var → Option (TreeTy d)}
    {hnd : Var → Option (NodeTy d)} {x : Var} (h : HndAgrees Γ hnd) :
    HndAgrees (removeTy Γ x) hnd := by
  intro z n hz
  exact h z n (removeTy_eq_some hz)

/-- A hand-off's handle function reads its own bound term's handle: the write's
own handle is what the fresh name takes over. -/
private theorem nextHnd_store {d : Layout} (hnd : Var → Option (NodeTy d)) (y x : Var)
    (a : Expr) :
    nextHnd hnd y (.store (.var x) 0 a) =
      (match hnd x with | some m => extendHnd hnd y m | none => hnd) := rfl

/-- A handle function handed the write of a hand-off agrees with the context that
hands the write's handle to the fresh name: the fresh name holds the written node
and every other name the context holds is one the function already agreed about,
because the handle the write went through is the one the fresh name takes over. -/
private theorem nextHnd_hndAgrees {d : Layout} {Γ : Var → Option (TreeTy d)}
    {hnd : Var → Option (NodeTy d)} {x y : Var} {a : Expr} {n : NodeTy d}
    (hh : HndAgrees Γ hnd) (hx : Γ x = some (.node n)) :
    HndAgrees (extendTy (removeTy Γ x) y (.node n))
      (nextHnd hnd y (.store (.var x) 0 a)) := by
  intro z n' hz
  by_cases hzy : z = y
  · subst hzy
    rw [extendTy_self] at hz
    cases hz
    rw [nextHnd_store, hh x n hx]
    simp [extendHnd]
  · rw [extendTy_of_ne hzy] at hz
    rw [nextHnd_store, hh x n hx]
    simp only [extendHnd, ite_eq_right hzy]
    exact hh z n' (removeTy_eq_some hz)

/-- A binding's handle function leaves every name but the fresh one as it was. -/
private theorem nextHnd_of_ne {d : Layout} {hnd : Var → Option (NodeTy d)} {y z : Var}
    {e : Expr} (hzy : z ≠ y) : nextHnd hnd y e z = hnd z := by
  unfold nextHnd
  cases hhe : handedHnd? hnd e with
  | none => rfl
  | some n => simp [extendHnd, hzy]

/-- A handle function handed the bound term of an observation binding agrees with
the continuation's context: the fresh name is held at an observation, which is
not a node, so only the names the function already agreed about survive, and
every other name is the function's own value there. -/
private theorem nextHnd_hndObs {d : Layout} {Γ : Var → Option (TreeTy d)}
    {hnd : Var → Option (NodeTy d)} {y : Var} {o : ObsDesc} {e₁ : Expr}
    (h : HndAgrees Γ hnd) : HndAgrees (extendTy Γ y (.obs o)) (nextHnd hnd y e₁) := by
  intro z n hz
  by_cases hzy : z = y
  · subst hzy
    rw [extendTy_self] at hz
    exact absurd hz (by simp)
  · rw [extendTy_of_ne hzy] at hz
    rw [nextHnd_of_ne hzy]
    exact h z n hz

/-- An environment extended at a fresh name holds closed values: the bound value
is closed and every value the environment held was. -/
theorem ClosedEnv.extend {ρ : VEnv} {y : Var} {v : Expr} (h : ClosedEnv ρ)
    (hv : Value v) (hc : Closed v) : ClosedEnv (VEnv.extend ρ y v) := by
  intro z w hz
  by_cases hzy : z = y
  · subst hzy
    rw [VEnv.extend_self] at hz
    obtain rfl : v = w := Option.some.inj hz
    exact ⟨hv, hc⟩
  · rw [VEnv.extend_of_ne hzy] at hz
    exact h z w hz

/-- An environment extended at a fresh observation name agrees with the context
extended with that observation: the bound value is unrooted and every other name
is the environment's own. -/
theorem ObsAgrees.extendObs {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv}
    {y : Var} {o : ObsDesc} {v : Expr} (h : ObsAgrees Γ ρ) (hv : hasProtected v = false) :
    ObsAgrees (extendTy Γ y (.obs o)) (VEnv.extend ρ y v) := by
  intro z o' hz
  by_cases hzy : z = y
  · subst hzy
    exact ⟨v, VEnv.extend_self _ _ _, hv⟩
  · rw [extendTy_of_ne hzy] at hz
    obtain ⟨w, hw, hp⟩ := h z o' hz
    exact ⟨w, by rw [VEnv.extend_of_ne hzy]; exact hw, hp⟩

/-- The context extended at a fresh name bound to a node agrees with an
environment that agrees with the context: the new name is not an observation. -/
theorem ObsAgrees.extendNode {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv}
    {y : Var} {n : NodeTy d} {v : Expr} (h : ObsAgrees Γ ρ) :
    ObsAgrees (extendTy Γ y (.node n)) (VEnv.extend ρ y v) := by
  intro z o hz
  by_cases hzy : z = y
  · subst hzy
    rw [extendTy_self] at hz
    exact absurd hz (by simp)
  · rw [extendTy_of_ne hzy] at hz
    obtain ⟨w, hw, hp⟩ := h z o hz
    exact ⟨w, by rw [VEnv.extend_of_ne hzy]; exact hw, hp⟩

/-- An environment agrees with the context the hand-off removes a name from. -/
theorem ObsAgrees.removeTy {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv}
    {x : Var} (h : ObsAgrees Γ ρ) : ObsAgrees (removeTy Γ x) ρ := by
  intro z o hz
  exact h z o (removeTy_eq_some hz)

/-- The field of a unary node the environment holds is a closed λPure value: the
environment's own agreement with the context reads it off the node. -/
theorem closedEnv_con1 {ρ : VEnv} {x : Var} {c : Ctor} {a : Expr} (h : ClosedEnv ρ)
    (hx : ρ x = some (.con1 c a)) : Value a ∧ Closed a := by
  have hboth := h x _ hx
  exact ⟨(value_con1_iff c a).mp hboth.1, hboth.2⟩

/-- The two fields of a binary node the environment holds are closed λPure values:
the environment's own agreement with the context reads them off the node. -/
theorem closedEnv_con2 {ρ : VEnv} {x : Var} {c : Ctor} {a b : Expr} (h : ClosedEnv ρ)
    (hx : ρ x = some (.con2 c a b)) : Value a ∧ Closed a ∧ Value b ∧ Closed b := by
  have hboth := h x _ hx
  exact ⟨(value_con2_iff c a b).mp hboth.1 |>.1, List.append_eq_nil_iff.mp hboth.2 |>.1,
    (value_con2_iff c a b).mp hboth.1 |>.2, List.append_eq_nil_iff.mp hboth.2 |>.2⟩

/-- A term equal to a quoted observation carries no protected node. -/
theorem hasProtected_of_eq_quoteEl {o : ObsDesc} {xel : ObsEl o} {v : Expr}
    (h : v = quoteEl o xel) : hasProtected v = false := by
  rw [h]
  exact quoteEl_hasProtected o xel

/-! ## The interpreter -/

/-- The interpreter of the admitted fragment: from the layout's state, the handle
function and the observation environment, the term evaluates to a value together
with the state it leaves, or `none` where its clauses have no case for the term's
shape.

The clauses follow the judgement's rules. An observation is built from the
environment's values and the constructors, and leaves the state alone. A read
looks the leaf's node up in the handle function and the detached quotation up in
the environment, and runs its continuation with the quotation bound; no state is
touched, because a read is detached. A descent looks the node up in the handle
function and the two field values up in the environment, and runs its
continuation with the node's components bound — each under the node's holder, the
spine's tail one offset further on. A write evaluates its operand and then looks
the node up: at a leaf the operand's quotation is decoded and written through the
leaf's own path, and at a struct node the operand is decoded and installed as the
component the write replaces. A binding evaluates the bound term and runs its
continuation with the fresh name bound to what it produced and with the handle
function the bound term hands on. A term no clause matches is not evaluated. -/
private def runTree (d : Layout) (hnd : Var → Option (NodeTy d)) (ρ : VEnv) (s : State d) :
    Expr → Option (Expr × State d)
  | .var x => (ρ x).map (fun v => (v, s))
  | .con0 c => some (.con0 c, s)
  | .con1 c b => (runTree d hnd ρ s b).map (fun p => (.con1 c p.1, p.2))
  | .con2 c f g =>
      (runTree d hnd ρ s f).bind (fun p =>
        (runTree d hnd ρ p.2 g).map (fun q => (.con2 c p.1 q.1, q.2)))
  | .matchC (.var x) c [y] body =>
      if c = rootTag then
        match ρ x with
        | some (.con1 c' v) =>
            if c' = rootTag then runTree d hnd (VEnv.extend ρ y v) s body else none
        | _ => none
      else none
  | .matchC (.var x) c [y, z] body =>
      if c = structTag then
        match hnd x with
        | some (.at wh pth (.struct a b) h) =>
            match ρ x with
            | some (.con2 c' v₁ v₂) =>
                if c' = structTag then
                  runTree d
                    (extendHnd
                      (extendHnd hnd y (.at wh (leftPath pth h) a (leftPath_at pth h))) z
                      (.at wh (rightPath pth h) b (rightPath_at pth h)))
                    (VEnv.extend (VEnv.extend ρ y v₁) z v₂) s body
                else none
            | _ => none
        | _ => none
      else if c = consTag then
        match hnd x with
        | some (.spine wh pth a h k) =>
            match ρ x with
            | some (.con2 c' v₁ v₂) =>
                if c' = consTag then
                  runTree d
                    (extendHnd
                      (extendHnd hnd y (.at wh (headPath pth a h k) a (headPath_at pth a h k))) z
                      (.spine wh pth a h (k + 1)))
                    (VEnv.extend (VEnv.extend ρ y v₁) z v₂) s body
                else none
            | _ => none
        | _ => none
      else none
  | .store (.var x) i b =>
      if i = 0 then
        (runTree d hnd ρ s b).bind (fun p =>
          match hnd x with
          | some (.at _ pth (.leaf o) h) =>
              (unquoteEl o p.1).map (fun xel => (.con1 rootTag p.1, (setLeaf ⟨pth, o, h⟩ xel s).1))
          | some (.at _ pth (.struct a _) h) =>
              match ρ x with
              | some (.con2 c' _ v₂) =>
                  if c' = structTag then
                    (unquoteVal a p.1).map (fun u =>
                      (.con2 structTag p.1 v₂, setStructLeft pth h u s))
                  else none
              | _ => none
          | _ => none)
      else none
  | .bind y e₁ e₂ =>
      (runTree d hnd ρ s e₁).bind (fun p =>
        runTree d (nextHnd hnd y e₁) (VEnv.extend ρ y p.1) p.2 e₂)
  | _ => none

/-! ## The observation evaluation -/

/-- A name the lowered context holds at an observation is a name the context
holds at that observation: the lowering maps an observation to itself, and a node
to a cell name, which is no observation. -/
private theorem obsEnv_obs {d : Layout} {Γ : Var → Option (TreeTy d)} {x : Var} {o : ObsDesc}
    (h : obsEnv Γ x = some (.obs o)) : ∃ o', Γ x = some (.obs o') ∧ o' = o := by
  cases hg : Γ x with
  | none => simp [obsEnv, hg] at h
  | some t =>
      cases t with
      | obs o' =>
          have h' : (Ty.obs o' : Ty) = Ty.obs o := by simpa [obsEnv, hg] using h
          exact ⟨o', by simp, Ty.obs.inj h'⟩
      | node n => simp [obsEnv, hg] at h

/-- An observation evaluates to its instance at the unchanged state: the
interpreter's constructor clauses build the node the instance is, a variable reads
the value the environment holds, and neither touches the state. The instance is a
closed λPure value that carries no protected node, which is the observation half
of the shape component. -/
private theorem runTree_obs {d : Layout} :
    ∀ {Γ : Var → Option (TreeTy d)} {e : Expr} {o : ObsDesc}, Obs (obsEnv Γ) e o →
      ∀ (hnd : Var → Option (NodeTy d)) {ρ : VEnv} {s : State d}, ClosedEnv ρ →
        ObsAgrees Γ ρ →
        runTree d hnd ρ s e = some (inst ρ e, s) ∧ Value (inst ρ e) ∧ Closed (inst ρ e) ∧
          hasProtected (inst ρ e) = false := by
  intro Γ e o h
  induction h with
  | var x hx hf =>
      intro hnd ρ s hcl hob
      obtain ⟨o', ho', hoo⟩ := obsEnv_obs hx
      subst hoo
      obtain ⟨w, hw, hp⟩ := hob x o' ho'
      have hinst : inst ρ (.var x) = w := by simp only [inst, hw, Option.getD_some]
      rw [hinst]
      refine ⟨?_, (hcl x w hw).1, (hcl x w hw).2, hp⟩
      simp only [runTree, hw, Option.map_some]
  | unit => intro hnd ρ s _ _; exact ⟨rfl, Value.con0 unitTag, rfl, rfl⟩
  | nat n => intro hnd ρ s _ _; exact ⟨rfl, Value.con0 n, rfl, rfl⟩
  | empty => intro hnd ρ s _ _; exact ⟨rfl, Value.con0 emptyTag, rfl, rfl⟩
  | full n =>
      intro hnd ρ s _ _
      refine ⟨?_, Value.con1 (Value.con0 n), rfl,
        hasProtected_con1_ne (by decide) (hasProtected_con0 n)⟩
      simp only [runTree, inst, Option.map_some]
  | pair ha hb iha ihb =>
      intro hnd ρ s hcl hob
      obtain ⟨hr₁, hv₁, hc₁, hp₁⟩ := iha hnd (s := s) hcl hob
      obtain ⟨hr₂, hv₂, hc₂, hp₂⟩ := ihb hnd (s := s) hcl hob
      refine ⟨?_, Value.con2 hv₁ hv₂, ?_,
        hasProtected_con2_ne (by decide) (by decide) hp₁ hp₂⟩
      · simp only [runTree, inst, hr₁, hr₂, Option.bind_some, Option.map_some]
      · simp only [Closed, uses, inst, List.append_eq_nil_iff]
        exact ⟨hc₁, hc₂⟩

/-- A binding's clause: the bound term is evaluated first, and the continuation
runs on the state it left, with the fresh name bound to what it produced and with
the handle function the bound term hands on. -/
private theorem runTree_bind {d : Layout} (hnd : Var → Option (NodeTy d)) (ρ : VEnv)
    (s : State d) (y : Var) (e₁ e₂ : Expr) :
    runTree d hnd ρ s (.bind y e₁ e₂) =
      (runTree d hnd ρ s e₁).bind (fun p =>
        runTree d (nextHnd hnd y e₁) (VEnv.extend ρ y p.1) p.2 e₂) := rfl

/-- A node quotation evaluates to its own instance at the unchanged state: a
recipe's term is built from observations and constructors alone. -/
private theorem runTree_recipe {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv} :
    ∀ {a : Layout} {b : Expr} {u : State a}, Recipe Γ ρ a b u →
      ∀ (hnd : Var → Option (NodeTy d)) (s : State d), ClosedEnv ρ → ObsAgrees Γ ρ →
        runTree d hnd ρ s b = some (inst ρ b, s) := by
  intro a b u h
  induction h using Recipe.rec with
  | leaf hObs hden =>
      intro hnd s hcl hob
      obtain ⟨hrun, _, _, _⟩ := runTree_obs hObs hnd (s := s) hcl hob
      simp only [runTree, inst, hrun, Option.map_some]
  | struct hx hy ihx ihy =>
      intro hnd s hcl hob
      have hx' := ihx hnd s hcl hob
      have hy' := ihy hnd s hcl hob
      simp only [runTree, inst, hx', hy', Option.bind_some, Option.map_some]
  | arr h ih => exact ih
  | nil => intro _ s _ _; rfl
  | cons hx ht ihx iht =>
      intro hnd s hcl hob
      have hx' := ihx hnd s hcl hob
      have ht' := iht hnd s hcl hob
      simp only [runTree, inst, hx', ht', Option.bind_some, Option.map_some]

/-! ## The node quotations decode -/

/-- The instance of a node quotation decodes back to the state it quotes, is a
closed λPure value, and binds no name: a subtree replacement's operand is read
from the term alone. The two quotations — the node's and the spine's list — are
eliminated together, because each recurses through the other. -/
private theorem recipe_shape {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv} :
    ∀ {a : Layout} {b : Expr} {u : State a}, Recipe Γ ρ a b u →
      unquoteVal a (inst ρ b) = some u ∧ Value (inst ρ b) ∧ Closed (inst ρ b) ∧
        binders b = [] := by
  intro a b u h
  refine Recipe.rec
    (motive_1 := fun a b u _ =>
      unquoteVal a (inst ρ b) = some u ∧ Value (inst ρ b) ∧ Closed (inst ρ b) ∧
        binders b = [])
    (motive_2 := fun a b l _ =>
      unquoteSpine a (inst ρ b) = some l ∧ Value (inst ρ b) ∧ Closed (inst ρ b) ∧
        binders b = [])
    ?_ ?_ ?_ ?_ ?_ h
  · intro o b xel hObs hden
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [inst, hden, unquoteVal, unwrapRoot, reduceIte, Option.bind_some,
        unquoteEl_quoteEl]
    · rw [inst, hden]; exact Value.con1 (quoteEl_value _ _)
    · rw [inst, hden]; exact quoteEl_closed _ _
    · rw [show binders (.con1 rootTag b) = binders b from rfl, obs_binders_nil hObs]
  · intro a b x y u v hx hy ihx ihy
    refine ⟨?_, Value.con2 ihx.2.1 ihy.2.1, ?_, ?_⟩
    · simp only [inst, unquoteVal, structTag, reduceIte, ihx.1, ihy.1, Option.bind_some,
        Option.map_some]
    · simp only [Closed, uses, inst, List.append_eq_nil_iff]
      exact ⟨ihx.2.2.1, ihy.2.2.1⟩
    · simp only [binders, ihx.2.2.2, ihy.2.2.2, List.nil_append]
  · intro a b l hl ih
    refine ⟨?_, ih.2.1, ih.2.2.1, ih.2.2.2⟩
    simp only [unquoteVal, ih.1, Option.map_some]
  · refine ⟨?_, Value.con0 nilTag, rfl, rfl⟩
    simp only [inst, unquoteSpine, nilTag, reduceIte]
  · intro a b t u l hx ht ihx iht
    refine ⟨?_, Value.con2 ihx.2.1 iht.2.1, ?_, ?_⟩
    · simp only [inst, unquoteSpine, consTag, reduceIte, ihx.1, iht.1, Option.bind_some,
        Option.map_some]
    · simp only [Closed, uses, inst, List.append_eq_nil_iff]
      exact ⟨ihx.2.2.1, iht.2.2.1⟩
    · simp only [binders, ihx.2.2.2, iht.2.2.2, List.nil_append]

/-! ## The freshness of the bound names -/

/-- A name the environment holds is bound by no rule: every binder's name is
absent from the environment at the point it binds, and an environment only ever
grows, so a name the environment holds is never bound by a rule of the derivation.
This is the half of the freshness the substitution the reduction performs is read
at — the context's own freshness is what a read's or a descent's arm uses to tell
its binder from the names the context already carries. -/
theorem treeOwn_binders_fresh : ∀ {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv}
    {A : Account d} {s : State d} {e : Expr} {τ : TreeTy d} {v : Expr} {s' : State d},
    TreeOwn d Γ ρ A s e τ v s' → ∀ a, ρ a ≠ none → a ∉ binders e := by
  intro d₀ Γ₀ ρ₀ A₀ s₀ e₀ τ₀ v₀ s₀' h
  induction h with
  | obs hobs =>
      intro z _
      rw [obs_binders_nil hobs]
      exact List.not_mem_nil
  | read x y body hx hval hden hid hpath hobs hread hy hρy hbody ih =>
      intro z hz hmem
      have hzy : z ≠ y := fun he => hz (by rw [he]; exact hρy)
      have hzb : z ∉ binders body := ih z (by
        intro hcontra
        rw [VEnv.extend_of_ne hzy] at hcontra
        exact hz hcontra)
      simp only [binders, List.nil_append] at hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hzy (List.mem_singleton.mp h)
      · exact hzb h
  | write x a hx hval hobs hden hacc hwrite =>
      intro z _ hmem
      have hb : binders (.store (.var x) 0 a) = [] := by
        rw [show binders (.store (.var x) 0 a) = binders a from rfl, obs_binders_nil hobs]
      rw [hb] at hmem
      exact List.not_mem_nil hmem
  | writeSub x b hx hval hrec hacc =>
      intro z _ hmem
      have hb : binders (.store (.var x) 0 b) = [] := by
        rw [show binders (.store (.var x) 0 b) = binders b from rfl, (recipe_shape hrec).2.2.2]
      rw [hb] at hmem
      exact List.not_mem_nil hmem
  | descendStruct x y z body hx hval hy hρy hz hρz hyz hbody ih =>
      intro zz hzz hmem
      have hzy : zz ≠ y := fun he => hzz (by rw [he]; exact hρy)
      have hzz' : zz ≠ z := fun he => hzz (by rw [he]; exact hρz)
      have hzb : zz ∉ binders body := ih zz (by
        intro hcontra
        rw [VEnv.extend_of_ne hzz', VEnv.extend_of_ne hzy] at hcontra
        exact hzz hcontra)
      simp only [binders, List.nil_append] at hmem
      rcases List.mem_append.mp hmem with h | h
      · rcases List.mem_cons.mp h with h | h
        · exact hzy h
        · exact hzz' (List.mem_singleton.mp h)
      · exact hzb h
  | descendSpine x y z body hx hval hy hρy hz hρz hyz hbody ih =>
      intro zz hzz hmem
      have hzy : zz ≠ y := fun he => hzz (by rw [he]; exact hρy)
      have hzz' : zz ≠ z := fun he => hzz (by rw [he]; exact hρz)
      have hzb : zz ∉ binders body := ih zz (by
        intro hcontra
        rw [VEnv.extend_of_ne hzz', VEnv.extend_of_ne hzy] at hcontra
        exact hzz hcontra)
      simp only [binders, List.nil_append] at hmem
      rcases List.mem_append.mp hmem with h | h
      · rcases List.mem_cons.mp h with h | h
        · exact hzy h
        · exact hzz' (List.mem_singleton.mp h)
      · exact hzb h
  | handoff x y a e₂ hx h₁ hy hρy h₂ ih₁ ih₂ =>
      intro z hz hmem
      have hzy : z ≠ y := fun he => hz (by rw [he]; exact hρy)
      have hb₁ : z ∉ binders (.store (.var x) 0 a) := ih₁ z hz
      have hb₂ : z ∉ binders e₂ := ih₂ z (by
        intro hcontra
        rw [VEnv.extend_of_ne hzy] at hcontra
        exact hz hcontra)
      simp only [binders] at hmem
      rcases List.mem_cons.mp hmem with h | h
      · exact hzy h
      · rcases List.mem_append.mp h with h | h
        · exact hb₁ h
        · exact hb₂ h
  | obsBind y e₁ e₂ h₁ hy hρy h₂ ih₁ ih₂ =>
      intro z hz hmem
      have hzy : z ≠ y := fun he => hz (by rw [he]; exact hρy)
      have hb₁ : z ∉ binders e₁ := ih₁ z hz
      have hb₂ : z ∉ binders e₂ := ih₂ z (by
        intro hcontra
        rw [VEnv.extend_of_ne hzy] at hcontra
        exact hz hcontra)
      simp only [binders] at hmem
      rcases List.mem_cons.mp hmem with h | h
      · exact hzy h
      · rcases List.mem_append.mp h with h | h
        · exact hb₁ h
        · exact hb₂ h

/-! ## Substituting into the instance -/

/-- Extending an environment at two distinct names commutes: the two bindings are
of different names, so neither shadows the other. -/
theorem VEnv.extend_comm {ρ : VEnv} {y z : Var} {v₁ v₂ : Expr} (hyz : y ≠ z) :
    VEnv.extend (VEnv.extend ρ y v₁) z v₂ = VEnv.extend (VEnv.extend ρ z v₂) y v₁ := by
  funext w
  by_cases hwy : w = y
  · subst hwy
    simp [VEnv.extend, hyz]
  · by_cases hwz : w = z
    · subst hwz
      simp [VEnv.extend, hwy]
    · simp [VEnv.extend, hwy, hwz]

/-- Substituting a name the term does not bind into its instance is extending the
environment with the substituted value, at two names at once: the two-name form
of `subst_inst` a descent into a struct node, or along a spine, substitutes its
two binders with. -/
theorem subst_two_inst {ρ : VEnv} {y z : Var} {v₁ v₂ : Expr} (hyz : y ≠ z)
    (hy : ρ y = none) (hz : ρ z = none) (hc₁ : Closed v₁) (hc₂ : Closed v₂)
    (hρ : ∀ x w, ρ x = some w → Closed w) {body : Expr} (hby : y ∉ binders body)
    (hbz : z ∉ binders body) :
    subst y v₁ (subst z v₂ (inst ρ body)) =
      inst (VEnv.extend (VEnv.extend ρ y v₁) z v₂) body := by
  rw [subst_inst hz hc₂ hρ body hbz]
  rw [subst_inst (y := y) (v := v₁) (ρ := VEnv.extend ρ z v₂)
    (by rw [VEnv.extend_of_ne hyz, hy]) hc₁
    (fun x w hx => by
      by_cases hxz : x = z
      · subst hxz
        rw [VEnv.extend_self] at hx
        obtain rfl : v₂ = w := Option.some.inj hx
        exact hc₂
      · rw [VEnv.extend_of_ne hxz] at hx
        exact hρ x w hx) body hby]
  rw [VEnv.extend_comm hyz]

/-! ## The instance of a term, clause by clause

The instance of a term under an environment is read one constructor at a time:
the equations below are the recursion of `inst` written at the shapes the
judgement's rules conclude, so that a proof can unfold the instance at exactly the
constructor it needs and leave the rest of the term alone. -/

/-- The instance of a variable is the value the environment holds for it. -/
theorem inst_var (ρ : VEnv) (x : Var) : inst ρ (.var x) = (ρ x).getD (.var x) := rfl

/-- The instance of a node is the node of its fields' instances. -/
theorem inst_con2 (ρ : VEnv) (c : Ctor) (a b : Expr) :
    inst ρ (.con2 c a b) = .con2 c (inst ρ a) (inst ρ b) := rfl

/-- The instance of a match is the match of its subject's and its body's
instances. -/
theorem inst_matchC (ρ : VEnv) (s : Expr) (c : Ctor) (ys : List Var) (body : Expr) :
    inst ρ (.matchC s c ys body) = .matchC (inst ρ s) c ys (inst ρ body) := rfl

/-- The instance of a write is the write of its subject's and its operand's
instances. -/
theorem inst_store (ρ : VEnv) (s : Expr) (i : Nat) (v : Expr) :
    inst ρ (.store s i v) = .store (inst ρ s) i (inst ρ v) := rfl

/-- The instance of a binding is the binding of its two terms' instances. -/
theorem inst_bind (ρ : VEnv) (x : Var) (e₁ e₂ : Expr) :
    inst ρ (.bind x e₁ e₂) = .bind x (inst ρ e₁) (inst ρ e₂) := rfl

/-! ## The write clauses -/

/-- A write at a leaf node: the operand evaluates to its instance at the unchanged
state, the instance decodes to the observation the leaf holds, and the state the
clause leaves is the library's own leaf write. -/
private theorem runTree_store_leaf {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv}
    {hnd : Var → Option (NodeTy d)} {s : State d} {x : Var} {a : Expr} {o : ObsDesc}
    {xl : ObsEl o} {w : Nat} {p : Path d} {h : At p = .leaf o} {s' : State d}
    (hobs : Obs (obsEnv Γ) a o) (hcl : ClosedEnv ρ) (hob : ObsAgrees Γ ρ)
    (hndx : hnd x = some (.at w p (.leaf o) h)) (hden : inst ρ a = quoteEl o xl)
    (hwrite : setLeaf ⟨p, o, h⟩ xl s = (s', true)) :
    runTree d hnd ρ s (.store (.var x) 0 a) = some (.con1 rootTag (inst ρ a), s') ∧
      Value (inst ρ a) ∧ Closed (inst ρ a) := by
  obtain ⟨hrun, hval', hcl', _⟩ := runTree_obs hobs hnd (s := s) hcl hob
  refine ⟨?_, hval', hcl'⟩
  simp only [runTree, hndx, hrun, Option.bind_some, hden, unquoteEl_quoteEl, Option.map_some,
    hwrite, reduceIte]

/-- A write at a struct node: the operand is a node quotation, decoded into the
component's state and installed in the struct's own cell, and the value the clause
yields is the struct node of the operand's instance and the component the write
did not touch. -/
private theorem runTree_store_struct {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv}
    {hnd : Var → Option (NodeTy d)} {s : State d} {x : Var} {b : Expr} {a c : Layout}
    {w : Nat} {p : Path d} {h : At p = .struct a c} {u : State a} {v₁ v₂ : Expr}
    (hrec : Recipe Γ ρ a b u) (hval : ρ x = some (.con2 structTag v₁ v₂))
    (hcl : ClosedEnv ρ) (hob : ObsAgrees Γ ρ) (hndx : hnd x = some (.at w p (.struct a c) h)) :
    runTree d hnd ρ s (.store (.var x) 0 b) =
        some (.con2 structTag (inst ρ b) v₂, setStructLeft p h u s) ∧
      Value (inst ρ b) ∧ Closed (inst ρ b) := by
  obtain ⟨huq, hvb, hcb, _⟩ := recipe_shape hrec
  have hrun := runTree_recipe hrec hnd s hcl hob
  refine ⟨?_, hvb, hcb⟩
  simp only [runTree, hndx, hval, hrun, Option.bind_some, huq, Option.map_some, reduceIte]

/-! ## The simulation -/

/-- The simulation: an admitted term, evaluated by the interpreter on a state and
an environment agreeing with its context, returns exactly the value and the state
the judgement names — and the copying λPure reduction of the term's instance
reaches that value. `StepStar (inst ρ e) v` is a statement about the existing
`Scidonia.RC.Step`, not about a second evaluator.

The agreement of the handle function with the context is an *input* assumption:
the fragment's types do not carry the node a handle names, and it is the rules'
own nodes that the interpreter's clauses are read at. The environment's closedness
is what a read's detached quotation and a write's operand need, and the
observation agreement is what the shape component is read from. -/
theorem runTree_simulate : ∀ {d : Layout} {Γ : Var → Option (TreeTy d)} {ρ : VEnv}
    {A : Account d} {s : State d} {e : Expr} {τ : TreeTy d} {v : Expr} {s' : State d},
    TreeOwn d Γ ρ A s e τ v s' →
    ∀ {hnd : Var → Option (NodeTy d)}, HndAgrees Γ hnd → ClosedEnv ρ → ObsAgrees Γ ρ →
      runTree d hnd ρ s e = some (v, s') ∧ StepStar (inst ρ e) v ∧ Value v ∧ Closed v
        ∧ Shape τ v := by
  intro d₀ Γ₀ ρ₀ A₀ s₀ e₀ τ₀ v₀ s₀' h
  induction h with
  | obs hobs =>
      intro hnd _ hcl hob
      obtain ⟨hrun, hv, hc, hp⟩ := runTree_obs hobs hnd hcl hob
      exact ⟨hrun, StepStar.refl _, hv, hc, hp⟩
  | read x y body hx hval hden hid hpath hobs hread hy hρy hbody ih =>
      intro hnd hh hcl hob
      obtain ⟨hv, hc⟩ := closedEnv_con1 hcl hval
      have hprot := hasProtected_of_eq_quoteEl hden
      obtain ⟨hrun, hstep, hval', hcl', hsh⟩ :=
        ih (HndAgrees.extendObs hh) (ClosedEnv.extend hcl hv hc) (ObsAgrees.extendObs hob hprot)
      have hfresh : y ∉ binders body :=
        treeOwn_binders_fresh hbody y (by simp)
      refine ⟨?_, ?_, hval', hcl', hsh⟩
      · simp only [runTree, hval, reduceIte]
        exact hrun
      · rw [inst_matchC, inst_var, hval, Option.getD_some]
        refine StepStar.step
          (Root.toStep (Root.matchVal (Value.con1 hv) rfl (by simp [nodeFields]))) ?_
        simpa only [nodeFields, substAll,
          subst_inst hρy hc (fun z w hw => (hcl z w hw).2) body hfresh] using hstep
  | write x a hx hval hobs hden hacc hwrite =>
      intro hnd hh hcl hob
      obtain ⟨hrun, hval', hcl'⟩ := runTree_store_leaf hobs hcl hob (hh x _ hx) hden hwrite
      obtain ⟨hv, _⟩ := closedEnv_con1 hcl hval
      refine ⟨hrun, ?_, Value.con1 hval', ?_, trivial⟩
      · rw [inst_store, inst_var, hval, Option.getD_some]
        refine StepStar.step
          (Root.toStep (Root.storeVal (Value.con1 hv) hval' (by simp [slotUpdate])))
          (StepStar.refl _)
      · rw [hden]; exact quoteEl_closed _ _
  | writeSub x b hx hval hrec hacc =>
      intro hnd hh hcl hob
      obtain ⟨hrun, hvb, hcb⟩ := runTree_store_struct hrec hval hcl hob (hh x _ hx)
      obtain ⟨_, _, hv₂, hc₂⟩ := closedEnv_con2 hcl hval
      refine ⟨hrun, ?_, Value.con2 hvb hv₂, ?_, trivial⟩
      · rw [inst_store, inst_var, hval, Option.getD_some]
        refine StepStar.step
          (Root.toStep (Root.storeVal (hcl x _ hval).1 hvb (by simp [slotUpdate])))
          (StepStar.refl _)
      · simp only [Closed, uses, List.append_eq_nil_iff]
        exact ⟨hcb, hc₂⟩
  | descendStruct x y z body hx hval hy hρy hz hρz hyz hbody ih =>
      intro hnd hh hcl hob
      obtain ⟨hv₁, hc₁, hv₂, hc₂⟩ := closedEnv_con2 hcl hval
      obtain ⟨hrun, hstep, hval', hcl', hsh⟩ :=
        ih (HndAgrees.extendNode (HndAgrees.extendNode hh))
          (ClosedEnv.extend (ClosedEnv.extend hcl hv₁ hc₁) hv₂ hc₂)
          (ObsAgrees.extendNode (ObsAgrees.extendNode hob))
      have hndx := hh x _ hx
      have hfy : y ∉ binders body :=
        treeOwn_binders_fresh hbody y (by simp [VEnv.extend, hyz])
      have hfz : z ∉ binders body :=
        treeOwn_binders_fresh hbody z (by simp)
      refine ⟨?_, ?_, hval', hcl', hsh⟩
      · simp only [runTree, hndx, hval, reduceIte]
        exact hrun
      · rw [inst_matchC, inst_var, hval, Option.getD_some]
        refine StepStar.step
          (Root.toStep (Root.matchVal (hcl x _ hval).1 rfl (by simp [nodeFields]))) ?_
        rw [nodeFields]
        simp only [substAll]
        rw [subst_two_inst hyz hρy hρz hc₁ hc₂ (fun z w hw => (hcl z w hw).2) (body := body)
          hfy hfz]
        exact hstep
  | descendSpine x y z body hx hval hy hρy hz hρz hyz hbody ih =>
      intro hnd hh hcl hob
      obtain ⟨hv₁, hc₁, hv₂, hc₂⟩ := closedEnv_con2 hcl hval
      obtain ⟨hrun, hstep, hval', hcl', hsh⟩ :=
        ih (HndAgrees.extendNode (HndAgrees.extendNode hh))
          (ClosedEnv.extend (ClosedEnv.extend hcl hv₁ hc₁) hv₂ hc₂)
          (ObsAgrees.extendNode (ObsAgrees.extendNode hob))
      have hndx := hh x _ hx
      have hfy : y ∉ binders body :=
        treeOwn_binders_fresh hbody y (by simp [VEnv.extend, hyz])
      have hfz : z ∉ binders body :=
        treeOwn_binders_fresh hbody z (by simp)
      refine ⟨?_, ?_, hval', hcl', hsh⟩
      · simp only [runTree, hndx, hval, reduceIte]
        exact hrun
      · rw [inst_matchC, inst_var, hval, Option.getD_some]
        refine StepStar.step
          (Root.toStep (Root.matchVal (hcl x _ hval).1 rfl (by simp [nodeFields]))) ?_
        rw [nodeFields]
        simp only [substAll]
        rw [subst_two_inst hyz hρy hρz hc₁ hc₂ (fun z w hw => (hcl z w hw).2) (body := body)
          hfy hfz]
        exact hstep
  | handoff x y a e₂ hx h₁ hy hρy h₂ ih₁ ih₂ =>
      intro hnd hh hcl hob
      obtain ⟨hrun₁, hstep₁, hv₁, hc₁, hsh₁⟩ := ih₁ hh hcl hob
      obtain ⟨hrun₂, hstep₂, hval₂, hcl₂, hsh₂⟩ :=
        ih₂ (nextHnd_hndAgrees (a := a) hh hx) (ClosedEnv.extend hcl hv₁ hc₁)
          (ObsAgrees.extendNode (ObsAgrees.removeTy hob))
      have hfresh : y ∉ binders e₂ := treeOwn_binders_fresh h₂ y (by simp)
      refine ⟨?_, ?_, hval₂, hcl₂, hsh₂⟩
      · rw [runTree_bind, hrun₁, Option.bind_some]
        exact hrun₂
      · rw [inst_bind]
        exact OwnershipTyped.StepStar.trans (stepStar_bindFun y _ hstep₁)
          (StepStar.step (Root.toStep (Root.bindVal hv₁))
            (by simpa only [subst_inst hρy hc₁ (fun z w hw => (hcl z w hw).2) e₂ hfresh]
                  using hstep₂))
  | obsBind y e₁ e₂ h₁ hy hρy h₂ ih₁ ih₂ =>
      intro hnd hh hcl hob
      obtain ⟨hrun₁, hstep₁, hv₁, hc₁, hsh₁⟩ := ih₁ hh hcl hob
      obtain ⟨hrun₂, hstep₂, hval₂, hcl₂, hsh₂⟩ :=
        ih₂ (nextHnd_hndObs (e₁ := e₁) hh) (ClosedEnv.extend hcl hv₁ hc₁)
          (ObsAgrees.extendObs hob hsh₁)
      have hfresh : y ∉ binders e₂ := treeOwn_binders_fresh h₂ y (by simp)
      refine ⟨?_, ?_, hval₂, hcl₂, hsh₂⟩
      · rw [runTree_bind, hrun₁, Option.bind_some]
        exact hrun₂
      · rw [inst_bind]
        exact OwnershipTyped.StepStar.trans (stepStar_bindFun y _ hstep₁)
          (StepStar.step (Root.toStep (Root.bindVal hv₁))
            (by simpa only [subst_inst hρy hc₁ (fun z w hw => (hcl z w hw).2) e₂ hfresh]
                  using hstep₂))

/-! ## The session -/

/-- The root node of a layout: a leaf's node is the leaf at the root path, a
struct's is the struct node there, and an array's is the spine of the array from
offset zero. -/
def rootNode : (d : Layout) → NodeTy d
  | .leaf o => .at 0 .here (.leaf o) rfl
  | .struct a b => .at 0 .here (.struct a b) rfl
  | .arr a => .spine 0 .here a rfl 0

/-- The name the session's context holds: the root node of the state. -/
def sessionName : Nat := 0

/-- The session's handle context: the root node, at `sessionName` and nowhere
else. -/
def rootCtx (d : Layout) : Var → Option (TreeTy d) :=
  fun x => if x = sessionName then some (.node (rootNode d)) else none

/-- The session's handle function: the root node, at `sessionName` and nowhere
else. -/
def rootHnd (d : Layout) : Var → Option (NodeTy d) :=
  fun x => if x = sessionName then some (rootNode d) else none

/-- The session's environment: the quotation of the state, at `sessionName` and
nowhere else. -/
def rootEnv (d : Layout) (s : State d) : VEnv :=
  fun x => if x = sessionName then some (cellVal d s) else none

/-- The handle function of the session agrees with its context. -/
theorem hndAgrees_rootCtx (d : Layout) : HndAgrees (rootCtx d) (rootHnd d) := by
  intro x n hx
  by_cases hxs : x = sessionName
  · rw [rootCtx, ite_eq_left hxs] at hx
    cases hx
    rw [rootHnd, ite_eq_left hxs]
  · rw [rootCtx, ite_eq_right hxs] at hx
    exact absurd hx (by simp)

/-- The session's environment holds a closed λPure value. -/
theorem closedEnv_rootEnv (d : Layout) (s : State d) : ClosedEnv (rootEnv d s) := by
  intro x w hx
  by_cases hxs : x = sessionName
  · rw [rootEnv, ite_eq_left hxs] at hx
    cases hx
    exact ⟨cellVal_value d s, cellVal_closed d s⟩
  · rw [rootEnv, ite_eq_right hxs] at hx
    exact absurd hx (by simp)

/-- The session's context holds no name at an observation, so the observation
agreement holds there vacuously. -/
theorem obsAgrees_rootCtx (d : Layout) (s : State d) : ObsAgrees (rootCtx d) (rootEnv d s) := by
  intro x o hx
  by_cases hxs : x = sessionName
  · rw [rootCtx, ite_eq_left hxs] at hx
    exact absurd hx (by simp)
  · rw [rootCtx, ite_eq_right hxs] at hx
    exact absurd hx (by simp)

/-- The value-level evaluation of an admitted program: the private interpreter run
on the session's configuration and state, returning only the value it produced.
The state is the caller's own — the library's layout state — and the session's
context and environment are created here, so the evaluation names no handle a
caller could hold. -/
def evalTree (d : Layout) (s : State d) (e : Expr) : Option Expr :=
  (runTree d (rootHnd d) (rootEnv d s) s e).map (fun p => p.1)

/-! ## The instance of a closed program -/

/-- A term every variable occurrence of which the environment does not hold is its
own instance, at both the occurrences the term uses and the names it binds: the
instance of a term is the term itself where the environment answers nothing. -/
private theorem inst_eq_self_of_none (ρ : VEnv) : ∀ e : Expr,
    (∀ x, x ∈ uses e → ρ x = none) → (∀ x, x ∈ binders e → ρ x = none) → inst ρ e = e := by
  intro e
  induction e with
  | var x =>
      intro huses _
      have hx : ρ x = none := huses x (by simp [uses])
      simp only [inst, hx, Option.getD_none]
  | lam x body ih =>
      intro huses hbind
      have ih' := ih
        (fun y hy => by
          by_cases hyx : y = x
          · exact hbind y (by simp [binders, hyx])
          · exact huses y (by simp [uses, hy, hyx]))
        (fun y hy => hbind y (by simp [binders, hy]))
      simp only [inst, ih']
  | app f a ihf iha =>
      intro huses hbind
      have ihf' := ihf (fun x hx => huses x (by simp [uses, hx]))
        (fun x hx => hbind x (by simp [binders, hx]))
      have iha' := iha (fun x hx => huses x (by simp [uses, hx]))
        (fun x hx => hbind x (by simp [binders, hx]))
      simp only [inst, ihf', iha']
  | bind x e₁ e₂ ih₁ ih₂ =>
      intro huses hbind
      have ih₁' := ih₁ (fun y hy => huses y (by simp [uses, hy]))
        (fun y hy => hbind y (by simp [binders, hy]))
      have ih₂' := ih₂
        (fun y hy => by
          by_cases hyx : y = x
          · exact hbind y (by simp [binders, hyx])
          · exact huses y (by simp [uses, hy, hyx]))
        (fun y hy => hbind y (by simp [binders, hy]))
      simp only [inst, ih₁', ih₂']
  | matchC s c ys body ihs ihb =>
      intro huses hbind
      have ihs' := ihs (fun x hx => huses x (by simp [uses, hx]))
        (fun x hx => hbind x (by simp [binders, hx]))
      have ihb' := ihb
        (fun y hy => by
          by_cases hyy : y ∈ ys
          · exact hbind y (by simp [binders, hyy])
          · exact huses y (by simp [uses, hy, hyy]))
        (fun y hy => hbind y (by simp [binders, hy]))
      simp only [inst, ihs', ihb']
  | dup x e ih =>
      intro huses hbind
      have ih' := ih (fun y hy => huses y (by simp [uses, hy]))
        (fun y hy => hbind y (by simp [binders, hy]))
      simp only [inst, ih']
  | drop x e ih =>
      intro huses hbind
      have ih' := ih (fun y hy => huses y (by simp [uses, hy]))
        (fun y hy => hbind y (by simp [binders, hy]))
      simp only [inst, ih']
  | con0 c => intro _ _; rfl
  | con1 c a ih => intro huses hbind; simp only [inst, ih huses hbind]
  | con2 c a b iha ihb =>
      intro huses hbind
      simp only [inst, iha (fun x hx => huses x (by simp [uses, hx]))
        (fun x hx => hbind x (by simp [binders, hx])),
        ihb (fun x hx => huses x (by simp [uses, hx]))
        (fun x hx => hbind x (by simp [binders, hx]))]
  | store s i w ihs ihw =>
      intro huses hbind
      have ihs' := ihs (fun x hx => huses x (by simp [uses, hx]))
        (fun x hx => hbind x (by simp [binders, hx]))
      have ihw' := ihw (fun x hx => huses x (by simp [uses, hx]))
        (fun x hx => hbind x (by simp [binders, hx]))
      simp only [inst, ihs', ihw']

/-- A closed program whose binders are all names other than `sessionName` is its
own instance at the session's environment: the session's environment holds
`sessionName` alone, and the program neither uses it free nor binds it. -/
theorem inst_rootEnv_eq {d : Layout} {s : State d} {e : Expr} (hc : Closed e)
    (h0 : sessionName ∉ binders e) : inst (rootEnv d s) e = e := by
  refine inst_eq_self_of_none (rootEnv d s) e ?_ ?_
  · intro x hx
    rw [Closed] at hc
    rw [hc] at hx
    exact absurd hx List.not_mem_nil
  · intro x hx
    have hx' : x ≠ sessionName := fun he => h0 (he ▸ hx)
    simp only [rootEnv, ite_eq_right hx']

/-! ## The public consequences -/

/-- The agreement at the session: an admitted program's evaluation returns the
value the judgement names, and the copying λPure reduction of the program's
instance reaches that value. -/
theorem evalTree_sound {d : Layout} {s : State d} {e : Expr} {τ : TreeTy d} {v : Expr}
    {s' : State d} {A : Account d}
    (h : TreeOwn d (rootCtx d) (rootEnv d s) A s e τ v s')
    (hs : StepStar (inst (rootEnv d s) e) v) (hv : Value v) : evalTree d s e = some v := by
  obtain ⟨hrun, hstep, hval, _, _⟩ :=
    runTree_simulate h (hndAgrees_rootCtx d) (closedEnv_rootEnv d s) (obsAgrees_rootCtx d s)
  have hsv : v = v := OwnershipTyped.stepStar_value_unique hstep hval hs hv
  rw [evalTree, hrun]
  show some v = some v
  exact congrArg some hsv

/-- The agreement at the session for a closed program: the copying reduction of
the program itself reaches the value its evaluation returns, because a closed
program that binds no `sessionName` is its own instance at the session's
environment. -/
theorem evalTree_sound_closed {d : Layout} {s : State d} {e : Expr} {τ : TreeTy d} {v : Expr}
    {s' : State d} {A : Account d}
    (h : TreeOwn d (rootCtx d) (rootEnv d s) A s e τ v s') (hc : Closed e)
    (h0 : sessionName ∉ binders e) (hs : StepStar e v) (hv : Value v) :
    evalTree d s e = some v :=
  evalTree_sound h (by rw [inst_rootEnv_eq hc h0]; exact hs) hv

/-- Totality: every admitted program's evaluation returns a value, and the copying
λPure reduction of the program's instance reaches that same value. -/
theorem evalTree_total {d : Layout} {s : State d} {e : Expr} {τ : TreeTy d} {A : Account d}
    {v : Expr} {s' : State d} (h : TreeOwn d (rootCtx d) (rootEnv d s) A s e τ v s') :
    ∃ v', evalTree d s e = some v' ∧ StepStar (inst (rootEnv d s) e) v' ∧ Value v' := by
  obtain ⟨hrun, hstep, hval, _, _⟩ :=
    runTree_simulate h (hndAgrees_rootCtx d) (closedEnv_rootEnv d s) (obsAgrees_rootCtx d s)
  have hgoal : evalTree d s e = some v := by
    rw [evalTree, hrun]
    show some v = some v
    rfl
  exact ⟨v, hgoal, hstep, hval⟩

/-- The quotation lemma: an admitted program of an observation type evaluates to a
value that carries no protected node, so no handle, subtree or array is among the
values the session returns. -/
theorem evalTree_no_protected {d : Layout} {s : State d} {e : Expr} {o : ObsDesc}
    {A : Account d} {v : Expr} {s' : State d}
    (h : TreeOwn d (rootCtx d) (rootEnv d s) A s e (.obs o) v s') {w : Expr}
    (hav : evalTree d s e = some w) : hasProtected w = false := by
  obtain ⟨hrun, _, _, _, hsh⟩ :=
    runTree_simulate h (hndAgrees_rootCtx d) (closedEnv_rootEnv d s) (obsAgrees_rootCtx d s)
  have hwv : w = v := by
    rw [evalTree, hrun] at hav
    simp only [Option.map_some] at hav
    exact (Option.some.inj hav).symm
  rw [hwv]
  exact hsh

/-! ## The runner -/

/-- The `IO` description over the private interpreter on the session's
configuration and state: it returns only the value the interpreter produced, and a
program the judgement does not admit fails the action rather than returning a
value, which the totality theorem makes unreachable for an admitted one. It is the
interpreter's runner and not a supported execution route: the equation below is
the whole of what is stated about it. -/
def runTreeIO (d : Layout) (s : State d) (e : Expr) {τ : TreeTy d} {v : Expr}
    {s' : State d} {A : Account d} (_h : TreeOwn d (rootCtx d) (rootEnv d s) A s e τ v s') :
    IO Expr := do
  match runTree d (rootHnd d) (rootEnv d s) s e with
  | some (w, _) => return w
  | none =>
      throw (IO.userError "Scidonia.RC.TreeOwnership.runTreeIO: the program did not evaluate")

/-- The runner's single `return`: under the evaluation the runner is the `pure`
return of the value the copying reduction reaches. This is an equality of Lean
`IO` *descriptions* — the runner's single `return` — and not a statement about
executing `IO`. -/
theorem runTreeIO_of_evalTree {d : Layout} {s : State d} {e : Expr} {τ : TreeTy d} {v : Expr}
    {s' : State d} {A : Account d}
    (h : TreeOwn d (rootCtx d) (rootEnv d s) A s e τ v s')
    (_hs : StepStar (inst (rootEnv d s) e) v) (_hv : Value v) : runTreeIO d s e h = pure v := by
  obtain ⟨hrun, _, _, _, _⟩ :=
    runTree_simulate h (hndAgrees_rootCtx d) (closedEnv_rootEnv d s) (obsAgrees_rootCtx d s)
  simp only [runTreeIO, hrun]

end TreeOwnership

end Scidonia.RC
