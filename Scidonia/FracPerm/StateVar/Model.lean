/-
The generic small-step model of a lawful state variable, and what it proves.

This is the generic counterpart of `Scidonia.FracPerm.Structured.Model`: the
same command trees, the same share discipline, the same schedule-independence
argument, but stated over an arbitrary `LawfulStateVar` instead of the array.
Nothing here is executable client code. The model gives the recipes of
`Scidonia.FracPerm.StateVar.Surface` their meaning and proves the ownership
properties the interface's shape is meant to guarantee for *every* lawful
instance, and `Scidonia.FracPerm.StateVar.Array` instantiates it at the array,
translating the structured interface's own trees by `liftR`/`liftP`.

The declarations take the instance as an explicit argument (`inst`), because the
recipes and the model's types depend on the instance's result family; the
theorems of this module state their instance as an ordinary implicit argument,
so a client writes `step_read h`, not `step_read inst h`.

## The model

A read phase is a `Thread`: a running subtree at a share `q`, or a join waiting
for two children that were forked from one. `Step s` is the small-step relation
over threads of a fixed logical state `s`; its congruence rules (`left`/`right`)
are what let the two branches of a fork run in either order or overlap, while
the sequential denotation `run` runs the left branch and then the right one.

A program is a `PConf`: `exclusive` when it holds the state, so that its
writer's authority is `1`, and `reading` while a read phase's subtree runs, with
the writer's authority `0`. `PStep` relates program configurations, and a
`write` step exists only in `exclusive`.

Shares are `Rat`: the root read phase has share `1`, a fork gives each child
half, a join restores the parent's share. `WF` states that invariant for
threads, `WFtree`/`WFptree` for the trees they are built from, and `WFConf` for
configurations — where it also requires the state to be `Valid`, which is what
makes `pstep_wf` use the instance's `replace_valid`.

## What is proved, and what it covers

* Primitive observations (`step_read`, `primitive_detached`): a `read` step's
  target is exactly the continuation applied to what the operation observed, and
  the encoding of what a primitive read observes of a valid state is detached
  from every root (`LawfulStateVar.observe_detached`). The observation a client
  receives is the operation's `Result`, never the state.
* Replay from observations (`replay_trace`, `replay_append`): `replay` runs a
  tree from a recorded list of observations with no state at all, and replaying
  the observations the sequential denotation makes returns that denotation. A
  trace entry carries its operation, so a trace cannot be consumed by a
  different operation. This is the semantic statement that a reader's result is
  a function of its observations; it cannot speak about physical aliasing.
* Fraction conservation (`wf_leafSum`, `wf_sharesPositive`, `wf_step`): a `WF`
  thread's leaves sum to its share, `WF` survives every step, and a positive
  share makes every leaf's share positive.
* Exclusion (`reading_step_is_read_or_leave`, `reading_share_is_one`,
  `reading_writer_authority_zero`): no `write` step has a source in a `reading`
  configuration, so a write starts only from a configuration whose writer
  authority is `1`; and a well-formed reading configuration's readers hold the
  whole share, leaving the writer `0`.
* Joining (`wait_step`, the `leave` rule of `PStep`): a `wait` node becomes a
  `run` only by the join step, which needs both children terminated, so a
  reading configuration returns to `exclusive` only through a thread that is a
  single `run` of a `pure` reader.
* Write preservation (`write_step`, `pstep_wf`): a `write` step's target is the
  continuation applied to the instance's `replace`, and well-formedness —
  including the state's validity — survives it. Whether the replacement happens
  in place is not a theorem here; for the array it is run-time evidence from
  `ScidoniaInPlace`.
* Schedule independence (`eval_step`, `eval_unique`, `eval_run`, `eval_stepStar`,
  `eval_of_run`, `complete_run_value`): every complete run of a read phase,
  under any interleaving, ends at the value `run`'s sequential denotation
  computes.
* Conditional composition (`SafeTree`, `safe_result`): if a read tree's
  continuations may only be handed detached observations, then the value it
  computes satisfies the client's own result relation. This is stated as a
  relation rather than as an unconditional law, because a client continuation
  can return any Lean value and `.pure (.loc ℓ)` would refute an unconditional
  no-reference conclusion for an arbitrary result type.

## What is assumed

* The model covers the command trees. A client continuation is an arbitrary
  Lean function of observation results, and no theorem here says anything about
  what such a function computes beyond the replay theorem: that the result
  depends only on the observations.
* The state is abstracted to the one logical state. Nothing here says anything
  about Lean's compiler or runtime; for the array, the in-place property of a
  write is evidence from running, not a theorem.
* A read phase is a finite tree with finite shares: `WF` says nothing about a
  continuation that builds new work indefinitely, so there is no liveness claim.
  Failure is not modelled, because the interface has no failure primitive.
* The class's `observe_detached` is a statement about the chosen `Value`
  encoding; it is not a theorem about Lean's object graph. See
  `Scidonia.FracPerm.StateVar.Value`.
-/
import Scidonia.FracPerm.StateVar.Surface

namespace Scidonia.FracPerm.StateVar

/-- One primitive observation of an instance: the operation, and its result. -/
abbrev Obs {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp) : Type :=
  Σ o : ReadOp, inst.Result o

/-- The instance's read recipe: `RT inst α` is a read tree whose sequential
denotation computes an `α`. -/
abbrev RT {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp)
    (α : Type) : Type 1 :=
  RTree ReadOp inst.Result α

/-- The instance's program recipe; `PT inst α` as `RT inst α`. -/
abbrev PT {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp)
    (α : Type) : Type 1 :=
  PTree ReadOp inst.Result WriteOp α

/-! ## Read phases: threads, steps, and the value they compute -/

/-- A read phase being run: a running subtree at share `q`, or a join waiting
for the two children of a fork, with the continuation the fork will resume. -/
inductive Thread {σ Init ReadOp WriteOp : Type}
    (inst : LawfulStateVar σ Init ReadOp WriteOp) : Type → Type 1 where
  | run {α : Type} (q : Rat) (t : RT inst α) : Thread inst α
  | wait {α : Type} (q : Rat) {β γ : Type} (l : Thread inst β) (r : Thread inst γ)
      (k : β × γ → RT inst α) : Thread inst α

/-- The steps of a read phase over the fixed state `s`.

`read` hands its continuation exactly what the instance observed, and leaves the
state alone. `fork` turns a running fork into a join over its two children at
half the share; `left`/`right` let either child step, which is what lets the two
branches run in either order or at the same time; `join` resumes the
continuation and requires both children to have terminated. -/
inductive Step {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp)
    (s : σ) : {α : Type} → Thread inst α → Thread inst α → Prop where
  | read {q : Rat} {α : Type} {o : ReadOp} {k : inst.Result o → RT inst α} :
      Step inst s (.run q (.read o k)) (.run q (k (inst.observe o s)))
  | fork {q : Rat} {α β γ : Type} {l : RT inst β} {r : RT inst γ} {k : β × γ → RT inst α} :
      Step inst s (.run q (.fork l r k)) (.wait q (.run (q / 2) l) (.run (q / 2) r) k)
  | left {q : Rat} {α β γ : Type} {l l' : Thread inst β} {r : Thread inst γ}
      {k : β × γ → RT inst α} (hstep : Step inst s l l') :
      Step inst s (.wait q l r k) (.wait q l' r k)
  | right {q : Rat} {α β γ : Type} {l : Thread inst β} {r r' : Thread inst γ}
      {k : β × γ → RT inst α} (hstep : Step inst s r r') :
      Step inst s (.wait q l r k) (.wait q l r' k)
  | join {q q₁ q₂ : Rat} {α β γ : Type} {b : β} {c : γ} {k : β × γ → RT inst α} :
      Step inst s (.wait q (.run q₁ (.pure b)) (.run q₂ (.pure c)) k) (.run q (k (b, c)))

/-- The reflexive-transitive closure of a read phase's steps: a complete run of
a read phase, of any length, under any interleaving. -/
inductive StepStar {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp)
    (s : σ) : {α : Type} → Thread inst α → Thread inst α → Prop where
  | refl {α : Type} (t : Thread inst α) : StepStar inst s t t
  | tail {α : Type} {a b c : Thread inst α} (h : StepStar inst s a b)
      (hstep : Step inst s b c) : StepStar inst s a c

/-- Relates a thread to what it computes. It is a relation rather than a
function because a thread's termination is what is at stake: `Eval` says the
thread has a value, and `eval_run` shows the sequential denotation is one way to
have it. -/
inductive Eval {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp)
    (s : σ) : {α : Type} → Thread inst α → α → Prop where
  | pure {q : Rat} {α : Type} {a : α} : Eval inst s (.run q (.pure a)) a
  | read {q : Rat} {α : Type} {o : ReadOp} {k : inst.Result o → RT inst α} {v : α}
      (hstep : Eval inst s (.run q (k (inst.observe o s))) v) :
      Eval inst s (.run q (.read o k)) v
  | fork {q : Rat} {α β γ : Type} {l : RT inst β} {r : RT inst γ} {k : β × γ → RT inst α}
      {b : β} {c : γ} {v : α}
      (hl : Eval inst s (.run (q / 2) l) b) (hr : Eval inst s (.run (q / 2) r) c)
      (hk : Eval inst s (.run q (k (b, c))) v) : Eval inst s (.run q (.fork l r k)) v
  | wait {q : Rat} {α β γ : Type} {l : Thread inst β} {r : Thread inst γ}
      {k : β × γ → RT inst α} {b : β} {c : γ} {v : α}
      (hl : Eval inst s l b) (hr : Eval inst s r c)
      (hk : Eval inst s (.run q (k (b, c))) v) : Eval inst s (.wait q l r k) v

/-! ## Shares

A read phase's fractions are an invariant of the threads rather than a value a
client writes: `WFtree q t` says a read tree is well formed at share `q`, and
`WF q t` says a thread is. The root read phase holds `1`, a fork splits its share
in half, and a join restores the parent's share. `leafSum` counts the shares of
the active leaves; the theorems below say the count is the share, that no step
creates or loses a fraction, and that a positive share makes every leaf's share
positive. -/

/-- The share invariant of a read tree: a `read` runs at its share whatever it
observes; a fork gives each child half its share and resumes its continuation at
the parent's share. -/
def WFtree {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp)
    (q : Rat) : RT inst α → Prop
  | .pure _ => True
  | .read _ k => ∀ x, WFtree inst q (k x)
  | .fork l r k => WFtree inst (q / 2) l ∧ WFtree inst (q / 2) r ∧ ∀ p, WFtree inst q (k p)

/-- The share invariant of a read phase being run. A running subtree is well
formed at its share; a join's children are well formed at half its share and its
continuation at the whole of it. -/
def WF {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp)
    (q : Rat) : Thread inst α → Prop
  | .run q' t => q = q' ∧ WFtree inst q t
  | .wait q' l r k => q = q' ∧ WF inst (q / 2) l ∧ WF inst (q / 2) r ∧ ∀ p, WFtree inst q (k p)

/-- The shares of a thread's active leaves: a running subtree is one leaf at its
share, and a join's leaves are its children's. -/
def leafSum {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp) :
    Thread inst α → Rat
  | .run q _ => q
  | .wait _ l r _ => leafSum inst l + leafSum inst r

/-- Every active leaf's share is positive. -/
def sharesPositive {σ Init ReadOp WriteOp : Type}
    (inst : LawfulStateVar σ Init ReadOp WriteOp) : Thread inst α → Prop
  | .run q _ => 0 < q
  | .wait _ l r _ => sharesPositive inst l ∧ sharesPositive inst r

/-! ## Programs -/

/-- A program configuration: `exclusive` holds the state and the tree that is
left to run; `reading` runs a read phase's subtree, with the program to resume
once it terminates. -/
inductive PConf {σ Init ReadOp WriteOp : Type}
    (inst : LawfulStateVar σ Init ReadOp WriteOp) : Type 1 where
  | exclusive {α : Type} (s : σ) (t : PT inst α) : PConf inst
  | reading {α : Type} {β : Type} (s : σ) (th : Thread inst β) (k : β → PT inst α) :
      PConf inst

/-- The steps of a program. A `write` step exists only in the exclusive
configuration, where the writer's authority is `1`; `enter` starts a read phase
at share `1`; `read` moves the running subtree; `leave` resumes the program, and
only from a thread that is a single finished reader. -/
inductive PStep {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp) :
    PConf inst → PConf inst → Prop where
  | write {α : Type} {s : σ} {w : WriteOp} {k : Bool → PT inst α} :
      PStep inst (.exclusive s (.write w k))
        (.exclusive (inst.replace w s).1 (k (inst.replace w s).2))
  | enter {α β : Type} {s : σ} {r : RT inst β} {k : β → PT inst α} :
      PStep inst (.exclusive s (.phase r k)) (.reading s (.run 1 r) k)
  | read {β : Type} {s : σ} {th th' : Thread inst β} {k : β → PT inst α}
      (hstep : Step inst s th th') : PStep inst (.reading s th k) (.reading s th' k)
  | leave {β : Type} {s : σ} {a : β} {k : β → PT inst α} :
      PStep inst (.reading s (.run 1 (.pure a)) k) (.exclusive s (k a))

/-- The share invariant of a program tree: a `write` runs whatever the answer; a
read phase is well formed at share `1`, the whole state, and its continuation
too. -/
def WFptree {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp) :
    PT inst α → Prop
  | .pure _ => True
  | .write _ k => ∀ b, WFptree inst (k b)
  | .phase r k => WFtree inst 1 r ∧ ∀ a, WFptree inst (k a)

/-- The share and validity invariant of a program configuration: the state is
`Valid`, the tree that is left is well formed, and while a read phase runs, its
thread is well formed at share `1` and the program to resume is too. Every
configuration this relation reaches from `exclusive` therefore has the whole
share accounted for and an admissible state. -/
def WFConf {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp) :
    PConf inst → Prop
  | .exclusive s t => inst.Valid s ∧ WFptree inst t
  | .reading s th k => inst.Valid s ∧ WF inst 1 th ∧ ∀ a, WFptree inst (k a)

/-- The writer's authority of a configuration: the whole state while exclusive,
and nothing while a read phase runs. -/
def writerAuthority {σ Init ReadOp WriteOp : Type}
    (inst : LawfulStateVar σ Init ReadOp WriteOp) : PConf inst → Rat
  | .exclusive _ _ => 1
  | .reading _ th _ => 1 - leafSum inst th

/-- The share the active readers of a configuration hold. -/
def readerShare {σ Init ReadOp WriteOp : Type}
    (inst : LawfulStateVar σ Init ReadOp WriteOp) : PConf inst → Rat
  | .exclusive _ _ => 0
  | .reading _ th _ => leafSum inst th

/-! ## Conditional composition -/

/-- `SafeTree inst ℓ α P t` says the read tree `t` computes an `α` that satisfies
`P`, provided every value its continuations are handed is detached from `ℓ`:

* a `pure` result must satisfy `P` outright;
* a `read o k` may apply `k` only to values whose encoding is detached from `ℓ`,
  and must be safe there;
* a `fork l r k` supplies its own relations for the two branches and requires
  the fork's continuation to be safe on a pair of branch results that satisfy
  them. -/
inductive SafeTree {σ Init ReadOp WriteOp : Type} (inst : LawfulStateVar σ Init ReadOp WriteOp)
    (ℓ : Loc) : (α : Type) → (α → Prop) → RT inst α → Prop where
  | pure {α : Type} {P : α → Prop} {a : α} (h : P a) : SafeTree inst ℓ α P (.pure a)
  | read {α : Type} {P : α → Prop} {o : ReadOp} {k : inst.Result o → RT inst α}
      (h : ∀ x, NoRef ℓ (inst.encodeRead o x) → SafeTree inst ℓ α P (k x)) :
      SafeTree inst ℓ α P (.read o k)
  | fork {α β γ : Type} {P : α → Prop} {l : RT inst β} {r : RT inst γ}
      {k : β × γ → RT inst α} {Pₗ : β → Prop} {Pᵣ : γ → Prop}
      (hl : SafeTree inst ℓ β Pₗ l) (hr : SafeTree inst ℓ γ Pᵣ r)
      (hk : ∀ x y, Pₗ x → Pᵣ y → SafeTree inst ℓ α P (k (x, y))) :
      SafeTree inst ℓ α P (.fork l r k)

section
variable {σ Init ReadOp WriteOp : Type} [inst : LawfulStateVar σ Init ReadOp WriteOp]

/-! ## Observations, the sequential denotation, and replay

`run` is the sequential denotation of a read tree — its result and the
observations it makes — and `replay` runs a tree from recorded observations with
no state at all. -/

/-- The sequential denotation of a read tree against a state: its result and the
observations it makes, in order. A `read` observes the operation's result, a
fork runs the left branch and then the right one, and every continuation is
applied to what it observed. -/
def run (s : σ) : RT inst α → α × List (Obs inst)
  | .pure a => (a, [])
  | .read o k =>
    let r := run s (k (inst.observe o s))
    (r.1, ⟨o, inst.observe o s⟩ :: r.2)
  | .fork l r k =>
    let bl := run s l
    let br := run s r
    let bk := run s (k (bl.1, br.1))
    (bk.1, bl.2 ++ (br.2 ++ bk.2))

/-- The result the sequential denotation computes. -/
def val (s : σ) (t : RT inst α) : α := (run (inst := inst) s t).1

attribute [local instance] Classical.propDecidable

/-- Run a tree from a recorded list of observations, with no state at all. It
returns the result and the observations it did not consume, or `none` when the
tree asks for an observation the record does not supply.

A trace entry carries its operation, so a read of `o` accepts an entry only when
it is tagged `o`, and transports its value along the equality: a trace cannot be
consumed by a different operation, and no cast of a value to the wrong
operation's result type is possible. The function is noncomputable because
comparing two operations is a logical side condition, not something an instance
must decide; it is model-only and is not on any runtime path. -/
noncomputable def replay : RT inst α → List (Obs inst) → Option (α × List (Obs inst))
  | .pure a, tr => some (a, tr)
  | .read o k, tr =>
    match tr with
    | [] => none
    | ⟨o', v⟩ :: tr' =>
      if h : o' = o then replay (k (cast (congrArg inst.Result h) v)) tr'
      else none
  | .fork l r k, tr =>
    (replay l tr).bind fun bl =>
      (replay r bl.2).bind fun br =>
        replay (k (bl.1, br.1)) br.2

/-- The sequential denotation of a program tree against a state: a read phase's
value is `val`, and a `write` replaces the state and continues with whether the
instance's `replace` reported the write as taking effect.

This is the model's evaluator for the generic recipes, and it is public; it is
not a second runner of the array executor, which stays sealed
(`Scidonia.FracPerm.Structured.Executor.runFresh`). -/
def pval (s : σ) : PT inst α → α
  | .pure a => a
  | .write w k => pval (inst.replace w s).1 (k (inst.replace w s).2)
  | .phase r k => pval s (k (val (inst := inst) s r))

/-! ## The theorems -/

/-- A `read` step hands its continuation exactly what the instance observed of
`s`. -/
theorem step_read {s : σ} {q : Rat} {o : ReadOp} {k : inst.Result o → RT inst α}
    {u : Thread inst α} (h : Step inst s (.run q (.read o k)) u) :
    u = .run q (k (inst.observe o s)) := by
  cases h; rfl

/-- A primitive observation of a valid state is detached from every root: the
class's no-reference law, at the point a read step would hand it to a client. -/
theorem primitive_detached {s : σ} (hs : inst.Valid s) :
    NoRef ℓ (inst.encodeRead o (inst.observe o s)) :=
  inst.observe_detached ℓ o s hs

/-- Replaying a tree with further observations appended consumes only what the
tree asks for and leaves the rest: the result's list is the suffix it did not
consume. -/
theorem replay_append (extra : List (Obs inst)) :
    ∀ (t : RT inst α) (tr : List (Obs inst)) (r : α × List (Obs inst)),
      replay (inst := inst) t tr = some r →
      replay (inst := inst) t (tr ++ extra) = some (r.1, r.2 ++ extra) := by
  intro t
  induction t with
  | pure a =>
    intro tr r h
    cases r with
    | mk r1 r2 =>
      simp only [replay, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | read o k ih =>
    intro tr r h
    cases tr with
    | nil => simp [replay] at h
    | cons e tr =>
      obtain ⟨o', v⟩ := e
      simp only [replay, List.cons_append] at h ⊢
      by_cases hh : o' = o
      · rw [dite_eq_left hh] at h ⊢
        exact ih (cast (congrArg inst.Result hh) v) tr r h
      · rw [dite_eq_right hh] at h
        exact absurd h (by simp)
  | fork l r k ihl ihr ihk =>
    intro tr res h
    cases hl : replay (inst := inst) l tr with
    | none => simp [replay, hl] at h
    | some bl =>
      cases hr : replay (inst := inst) r bl.2 with
      | none => simp [replay, hl, hr] at h
      | some br =>
        have hk : replay (inst := inst) (k (bl.1, br.1)) br.2 = some res := by
          simpa [replay, hl, hr] using h
        have hla := ihl tr bl hl
        have hlb := ihr bl.2 br hr
        have hka := ihk (bl.1, br.1) br.2 res hk
        simp only [replay, hla, hlb, hka, Option.bind_some]

/-- Replaying the observations `run` makes returns `run`'s result, having
consumed the whole record: a read tree's result is a function of the
observations alone.

This is the semantic statement that a reader's result is a function of what it
observed. It cannot speak about physical aliasing, which is why the run-time
check exists for the array. -/
theorem replay_trace (s : σ) (t : RT inst α) :
    replay (inst := inst) t (run (inst := inst) s t).2 = some (val (inst := inst) s t, []) := by
  induction t with
  | pure a => rfl
  | read o k ih =>
    show replay (inst := inst) (.read o k)
        (run (inst := inst) s (.read o k)).2 = some (val (inst := inst) s (.read o k), [])
    simp only [run, val, replay]
    rw [dite_eq_left trivial]
    exact ih (inst.observe o s)
  | fork l r k ihl ihr ihk =>
    have hbl : replay (inst := inst) l (run (inst := inst) s l).2 =
        some ((run (inst := inst) s l).1, []) := by simpa [val] using ihl
    have hbr : replay (inst := inst) r (run (inst := inst) s r).2 =
        some ((run (inst := inst) s r).1, []) := by simpa [val] using ihr
    have hbk : replay (inst := inst) (k ((run (inst := inst) s l).1,
          (run (inst := inst) s r).1))
        (run (inst := inst) s (k ((run (inst := inst) s l).1,
          (run (inst := inst) s r).1))).2 =
        some ((run (inst := inst) s (k ((run (inst := inst) s l).1,
          (run (inst := inst) s r).1))).1, []) := by
      simpa [val] using ihk ((run (inst := inst) s l).1, (run (inst := inst) s r).1)
    have hla := replay_append (inst := inst)
      (extra := (run (inst := inst) s r).2 ++
        (run (inst := inst) s (k ((run (inst := inst) s l).1,
          (run (inst := inst) s r).1))).2)
      l (run (inst := inst) s l).2 ((run (inst := inst) s l).1, []) hbl
    have hlb := replay_append (inst := inst)
      (extra := (run (inst := inst) s (k ((run (inst := inst) s l).1,
        (run (inst := inst) s r).1))).2)
      r (run (inst := inst) s r).2 ((run (inst := inst) s r).1, []) hbr
    simp only [run, val, replay]
    rw [hla]
    simp only [Option.bind_some, List.nil_append]
    rw [hlb]
    simp only [Option.bind_some, List.nil_append]
    rw [hbk]

/-- Every step preserves the value a thread computes. -/
theorem eval_step : ∀ {s : σ} {α : Type} {t u : Thread inst α},
    Step inst s t u → ∀ v, Eval inst s t v → Eval inst s u v := by
  intro s α t u h
  induction h with
  | read => intro v hv; cases hv with | read hv => exact hv
  | fork => intro v hv; cases hv with | fork hb hc hk => exact .wait hb hc hk
  | left hstep ih => intro v hv; cases hv with | wait hl hr hk => exact .wait (ih _ hl) hr hk
  | right hstep ih => intro v hv; cases hv with | wait hl hr hk => exact .wait hl (ih _ hr) hk
  | join => intro v hv; cases hv with
    | wait hl hr hk =>
      cases hl with | pure =>
      cases hr with | pure =>
      exact hk

/-- A thread computes at most one value. -/
theorem eval_unique {s : σ} :
    ∀ {t : Thread inst α} {a : α}, Eval inst s t a → ∀ {b : α}, Eval inst s t b → a = b := by
  intro t a h1
  induction h1 with
  | pure => intro b h2; cases h2; rfl
  | read hstep ih => intro b h2; cases h2 with | read h2 => exact ih h2
  | fork hb hc hk ihb ihc ihk =>
    intro b h2
    cases h2 with
    | fork hb' hc' hk' =>
      have hbb : _ = _ := ihb hb'
      have hcc : _ = _ := ihc hc'
      rw [← hbb, ← hcc] at hk'
      exact ihk hk'
  | wait hl hr hk ihl ihr ihk =>
    intro b h2
    cases h2 with
    | wait hl' hr' hk' =>
      have hll : _ = _ := ihl hl'
      have hrr : _ = _ := ihr hr'
      rw [← hll, ← hrr] at hk'
      exact ihk hk'

/-- The sequential denotation computes a value the thread has: every complete run
of the read phase computes it. -/
theorem eval_run (s : σ) : ∀ (t : RT inst α) (q : Rat), Eval inst s (.run q t) (val s t) := by
  intro t
  induction t with
  | pure a => intro q; exact .pure
  | read o k ih => intro q; exact .read (ih (inst.observe o s) q)
  | fork l r k ihl ihr ihk =>
    intro q
    have h := Eval.fork (ihl (q / 2)) (ihr (q / 2)) (ihk (val s l, val s r) q)
    simpa [val, run] using h

/-- Every step of a run preserves the value the run computes. -/
theorem eval_stepStar {s : σ} {u v : Thread inst α} {x : α}
    (h : StepStar inst s u v) (hu : Eval inst s u x) : Eval inst s v x := by
  induction h with
  | refl => exact hu
  | tail _ hstep ih => exact eval_step hstep _ ih

/-- Along a complete run of a read phase, every thread computes the value the
sequential denotation computes: the run's own value is that value, whatever the
interleaving. -/
theorem eval_of_run {s : σ} {t : RT inst α} {t' : Thread inst α}
    (h : StepStar inst s (.run 1 t) t') (ha : Eval inst s t' a) : a = val s t := by
  have hev : Eval inst s t' (val s t) := eval_stepStar h (eval_run s t 1)
  exact (eval_unique hev ha).symm

/-- A read phase that reaches a finished run computes the sequential
denotation's value, under every interleaving. -/
theorem complete_run_value {s : σ} {t : RT inst α} {a : α}
    (h : StepStar inst s (.run 1 t) (.run 1 (.pure a))) : a = val s t :=
  eval_of_run h .pure

/-- A well-formed thread's leaves sum to its share: forking splits a share and
joining puts it back, and no share is counted twice. -/
theorem wf_leafSum : ∀ {t : Thread inst α}, ∀ {q : Rat}, WF inst q t → leafSum inst t = q := by
  intro t
  induction t with
  | run q' tree => intro q h; exact h.1.symm
  | wait q' l r k ihl ihr =>
    intro q h
    obtain ⟨_, hl, hr, _⟩ := h
    have h1 := ihl (q := q / 2) hl
    have h2 := ihr (q := q / 2) hr
    show leafSum inst l + leafSum inst r = q
    rw [h1, h2]
    grind

/-- A well-formed thread with a positive share has every leaf's share positive,
so a reader running at a positive share can never observe at share zero. -/
theorem wf_sharesPositive : ∀ {t : Thread inst α}, ∀ {q : Rat}, WF inst q t → 0 < q →
    sharesPositive inst t := by
  intro t
  induction t with
  | run q' tree =>
    intro q h hq
    rw [← h.1]
    exact hq
  | wait q' l r k ihl ihr =>
    intro q h hq
    obtain ⟨_, hl, hr, _⟩ := h
    have hq' : 0 < q / 2 := by grind
    exact ⟨ihl (q := q / 2) hl hq', ihr (q := q / 2) hr hq'⟩

/-- Every step preserves well-formedness: a fork splits a share and a join
restores it, and each congruence step moves well-formedness to the child that
stepped. -/
theorem wf_step : ∀ {s : σ} {α : Type} {t u : Thread inst α},
    Step inst s t u → ∀ q, WF inst q t → WF inst q u := by
  intro s α t u h
  induction h with
  | read => intro q hw; exact ⟨hw.1, hw.2 _⟩
  | fork => intro q hw; exact ⟨hw.1, ⟨congrArg (· / 2) hw.1, hw.2.1⟩, ⟨congrArg (· / 2) hw.1, hw.2.2.1⟩, hw.2.2.2⟩
  | left hstep ih => intro q hw; exact ⟨hw.1, ih (q / 2) hw.2.1, hw.2.2⟩
  | right hstep ih => intro q hw; exact ⟨hw.1, hw.2.1, ih (q / 2) hw.2.2.1, hw.2.2.2⟩
  | join => intro q hw; exact ⟨hw.1, hw.2.2.2 _⟩

/-- A `wait` node becomes a `run` only by the join step, which requires both
children to have terminated; every other step of a `wait` node yields a `wait`
node. This is why a read phase cannot be short-circuited: the congruence rules
move the join's own subtree, and only a terminated pair lets the continuation
run. -/
theorem wait_step {s : σ} {q : Rat} {α β γ : Type} {l : Thread inst β}
    {r : Thread inst γ} {k : β × γ → RT inst α} {u : Thread inst α}
    (h : Step inst s (.wait q l r k) u) :
    (∃ q' l' r', u = .wait q' l' r' k) ∨
    (∃ (q₁ q₂ : Rat) (b : β) (c : γ),
      l = .run q₁ (.pure b) ∧ r = .run q₂ (.pure c) ∧ u = .run q (k (b, c))) := by
  cases h with
  | left hstep => exact .inl ⟨_, _, _, rfl⟩
  | right hstep => exact .inl ⟨_, _, _, rfl⟩
  | join => exact .inr ⟨_, _, _, _, rfl, rfl, rfl⟩

/-- From a `reading` configuration a step is either another `read` step or the
`leave` step. The `write` rule's source is `exclusive`, so no write step has a
reading source: a write while a read phase runs is not a step of this relation.
-/
theorem reading_step_is_read_or_leave {s : σ} {th : Thread inst β}
    {k : β → PT inst α} {c' : PConf inst} (h : PStep inst (.reading s th k) c') :
    (∃ th', c' = .reading s th' k) ∨
    (∃ a, th = .run 1 (.pure a) ∧ c' = .exclusive s (k a)) := by
  cases h with
  | read hstep => exact .inl ⟨_, rfl⟩
  | leave => exact .inr ⟨_, rfl, rfl⟩

/-- A read-phase step leaves the state alone: no read primitive replaces it, so
the state a reader observes cannot change under it. -/
theorem reading_step_store {s s' : σ} {th th' : Thread inst β} {k : β → PT inst α}
    (h : PStep inst (.reading s th k) (.reading s' th' k)) : s' = s := by
  cases h with | read _ => rfl

/-- A `write` step's target: the continuation is told whether the write took
effect, and the state is exactly the one the instance's `replace` produced. -/
theorem write_step {s : σ} {w : WriteOp} {k : Bool → PT inst α} {c' : PConf inst}
    (h : PStep inst (.exclusive s (.write w k)) c') :
    c' = .exclusive (inst.replace w s).1 (k (inst.replace w s).2) := by
  cases h; rfl

/-- A well-formed reading configuration's readers hold the whole share —
`leafSum th = 1` — so the writer's authority is `0` while they run. -/
theorem reading_share_is_one {s : σ} {th : Thread inst β} {k : β → PT inst α}
    (hw : WFConf inst (.reading s th k)) : leafSum inst th = 1 := wf_leafSum hw.2.1

/-- A well-formed reading configuration's readers hold a positive share at every
leaf, so a read phase cannot be running at share zero. -/
theorem reader_share_positive {s : σ} {th : Thread inst β} {k : β → PT inst α}
    (hw : WFConf inst (.reading s th k)) : sharesPositive inst th :=
  wf_sharesPositive hw.2.1 (by grind)

/-- While a read phase runs, the writer's authority is `0`: the readers hold the
whole share. -/
theorem reading_writer_authority_zero {s : σ} {th : Thread inst β} {k : β → PT inst α}
    (hw : WFConf inst (.reading s th k)) :
    writerAuthority inst (.reading s th k) = 0 := by
  have h1 := reading_share_is_one hw
  show 1 - leafSum inst th = 0
  rw [h1]
  grind

/-- The writer's authority and the readers' shares add up to the whole in every
well-formed configuration: `1` for the writer while exclusive, and all of it out
with the readers — leaving the writer `0` — while a read phase runs. -/
theorem writer_authority_add {c : PConf inst} (hw : WFConf inst c) :
    writerAuthority inst c + readerShare inst c = 1 := by
  cases c with
  | exclusive s t => show (1 : Rat) + 0 = 1; grind
  | reading s th k =>
    have h1 := reading_share_is_one hw
    show (1 - leafSum inst th) + leafSum inst th = 1
    rw [h1]
    grind

/-- Every program step preserves well-formedness — including the state's
validity, which the `write` case obtains from the instance's `replace_valid` —
so every configuration reachable from an exclusive one has the whole share
accounted for and an admissible state. -/
theorem pstep_wf {c c' : PConf inst} (h : PStep inst c c') (hw : WFConf inst c) :
    WFConf inst c' := by
  cases h with
  | write => exact ⟨inst.replace_valid _ _ hw.1, hw.2 _⟩
  | enter => exact ⟨hw.1, ⟨rfl, hw.2.1⟩, hw.2.2⟩
  | read hstep => exact ⟨hw.1, wf_step hstep 1 hw.2.1, hw.2.2⟩
  | leave => exact ⟨hw.1, hw.2.2 _⟩

/-- A safe read tree of a valid state computes a value satisfying the client's
relation: the tree's result is detached whenever its continuations may only be
handed detached observations. -/
theorem safe_result {ℓ : Loc} {α : Type} {P : α → Prop} {t : RT inst α} {s : σ}
    (ht : SafeTree inst ℓ α P t) (hs : inst.Valid s) : P (val s t) := by
  induction ht generalizing s with
  | pure h => exact h
  | read hp ih =>
    rename_i o k
    exact ih (inst.observe o s) (inst.observe_detached ℓ o s hs) (s := s) hs
  | fork hl hr hk ihl ihr ihk =>
    rename_i α' P' l r k Pl Pr
    exact ihk (val s l) (val s r) (ihl (s := s) hs) (ihr (s := s) hs) (s := s) hs

end

end Scidonia.FracPerm.StateVar
