/-
The small-step model of the structured interface, and what it proves.

This file gives the command trees of `Scidonia.FracPerm.Structured.Surface`
their operational meaning and proves the ownership properties that the
interface's shape is meant to guarantee. Nothing here is executable client
code: the model exists to say precisely what the interface promises, and
`Scidonia.FracPerm.Structured.Executor` is what runs.

## The model

A read phase is a `Thread`: a running subtree at a share `q`, or a join waiting
for two children that were forked from one. `Step s` is the small-step relation
over threads for a fixed array `s`; its congruence rules (`left`/`right`) are
what let the two branches of a fork run in either order or overlap — the
relation has a step for every interleaving, while the shipped executor picks
one (left branch, then right branch).

A program is a `PConf`: `exclusive` when it holds the array, so that its
writer's authority is `1`, and `reading` while a read phase's subtree is
running, with the writer's authority `0`. `PStep` relates program
configurations, and a `set` step exists only in `exclusive`.

Shares are `Rat`: the root read phase has share `1`, a fork gives each child
half, a join restores the parent's share. `WF` states that invariant for
threads, and `WFtree`/`WFptree` for the trees out of which threads and programs
are built.

## What is proved, and what it covers

* Primitive observations (`step_get`, `step_size`, `reading_step_store`): a
  `get` step's target is exactly the continuation applied to `s[i]?`, a `size`
  step's exactly the continuation applied to `s.size`, and no read-phase step
  changes the store. A continuation's argument types are `Option UInt64` and
  `Nat` by construction, so nothing a read hands to a client can name the
  array.
* Replay from observations (`replay_trace`): `replay` runs a tree from a
  recorded list of observations with no array at all, and replaying the
  observations the sequential denotation makes returns that denotation. This is
  the semantic statement that a reader's result is a function of its
  observations; it cannot speak about physical aliasing.
* Fraction conservation (`wf_leafSum`, `wf_sharesPositive`): a `WF` thread's
  leaves sum to its share, `WF` survives every step, and a positive share makes
  every leaf's share positive.
* Exclusion (`reading_step_is_read_or_leave`, `reading_share_is_one`): no `set`
  step has a source in a `reading` configuration, so a write starts only from a
  configuration whose writer authority is `1`; and a well-formed reading
  configuration's readers hold the whole share, leaving the writer `0`.
* Joining (`wait_step`, the `leave` rule of `PStep`): a `wait` node becomes a
  `run` only by the join step, which needs both children terminated, so a
  reading configuration returns to `exclusive` only through a thread that is a
  single `run` of a `pure` reader — every descendant has terminated. The
  program level's `leave` rule is the only step from a reading to an exclusive
  configuration, and its source is exactly that finished run.
* Write preservation (`set_step`, `set_step_size`): a `set` step's target is
  the continuation applied to whether the index was in bounds, the array size
  is preserved, and an out-of-bounds index leaves the array alone. Whether the
  update happens in place is not a theorem here; that is run-time evidence from
  `ScidoniaInPlace`.
* Schedule independence (`eval_step`, `eval_unique`, `eval_run`): `Eval`
  relates a thread to the value it computes. Every step preserves it, a
  thread's value is unique, and the sequential denotation `val` computes it. So
  every complete run of a read phase, under any interleaving, ends at the value
  `val` computes, which is what makes the sequential executor a valid
  implementation of the fork/join semantics.
* The link to the shipped executor (`Executor.execR_eq_val`,
  `Executor.execP_eq_pval`): the executor's interpreters are the same
  recursions as `val` and `pval`, with `assertExclusiveArray` — the identity in
  the logic — in front of the in-place update.

`run`, `val` and `pval` are public, and they are the model: they evaluate a
command tree on an array the caller supplies. They are not a route to any
session's array — a session's array exists only inside `Executor.runFresh` — and
what the theorems above say is about them.

## What is assumed

* The model covers the command trees. A client continuation is an arbitrary
  Lean function of observation results, and no theorem here says anything about
  what such a function computes beyond the replay theorem: that the result
  depends only on the observations.
* The heap is abstracted to the one array. Nothing here says anything about
  Lean's compiler or runtime, and the in-place property of a `set` is evidence
  from running, not a theorem.
* A read phase is a finite tree with finite shares: `WF` says nothing about a
  continuation that builds new work indefinitely, so there is no liveness
  claim. Failure is not modelled, because the interface has no failure
  primitive.
-/
import Scidonia.FracPerm.Structured.Surface

namespace Scidonia.FracPerm.Structured

/-! ## Observations, the sequential denotation, and replay

`Obs` records a primitive observation: what `Reader.get` and `Reader.size`
yield. `run` is the sequential denotation of a read tree — its result and the
observations it makes — and `replay` runs a tree from recorded observations
with no array at all. -/

/-- One primitive observation: the element a `get` observed, or the size a
`size` observed. A recorded observation is a value detached from the array. -/
inductive Obs where
  /-- What `Reader.get` yielded. -/
  | get (o : Option UInt64) : Obs
  /-- What `Reader.size` yielded. -/
  | size (n : Nat) : Obs
deriving Repr, DecidableEq

/-- The sequential denotation of a read tree against an array: its result and
the observations it makes, in order. `get` observes `s[i]?`, `size` observes
`s.size`, a fork runs the left branch and then the right one, and every
continuation is applied to what it observed.

This is the recursion the shipped executor's read interpreter runs; see
`Executor.execR_eq_val`. -/
def run (s : Array UInt64) : RTree α → α × List Obs
  | .pure a => (a, [])
  | .get i k =>
    let r := run s (k s[i]?)
    (r.1, .get s[i]? :: r.2)
  | .size k =>
    let r := run s (k s.size)
    (r.1, .size s.size :: r.2)
  | .fork l r k =>
    let bl := run s l
    let br := run s r
    let bk := run s (k (bl.1, br.1))
    (bk.1, bl.2 ++ (br.2 ++ bk.2))

/-- The result the sequential denotation computes. -/
def val (s : Array UInt64) (t : RTree α) : α := (run s t).1

/-- Run a tree from a recorded list of observations, with no array at all. It
returns the result and the observations it did not consume, or `none` when the
tree asks for an observation the record does not supply.

Every value this function can use comes from the record: continuations are
applied to what the record supplies and to branch results, and the tree itself
carries no state. -/
def replay : RTree α → List Obs → Option (α × List Obs)
  | .pure a, tr => some (a, tr)
  | .get _ k, .get o :: tr => replay (k o) tr
  | .size k, .size n :: tr => replay (k n) tr
  | .fork l r k, tr =>
    (replay l tr).bind fun bl =>
      (replay r bl.2).bind fun br =>
        replay (k (bl.1, br.1)) br.2
  | _, _ => none

/-- Replaying a tree with further observations appended consumes only what the
tree asks for and leaves the rest: the result's list is the suffix it did not
consume. -/
theorem replay_append (extra : List Obs) :
    ∀ (t : RTree α) (tr : List Obs) (r : α × List Obs),
      replay t tr = some r → replay t (tr ++ extra) = some (r.1, r.2 ++ extra) := by
  intro t
  induction t with
  | pure a =>
    intro tr r h
    cases r with
    | mk r1 r2 =>
      simp only [replay, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | get i k ih =>
    intro tr r h
    cases tr with
    | nil => simp [replay] at h
    | cons o tr =>
      cases o with
      | get o => exact ih o tr r h
      | size n => simp [replay] at h
  | size k ih =>
    intro tr r h
    cases tr with
    | nil => simp [replay] at h
    | cons o tr =>
      cases o with
      | get o => simp [replay] at h
      | size n => exact ih n tr r h
  | fork l r k ihl ihr ihk =>
    intro tr res h
    cases hl : replay l tr with
    | none => simp [replay, hl] at h
    | some bl =>
      cases hr : replay r bl.2 with
      | none => simp [replay, hl, hr] at h
      | some br =>
        have hk : replay (k (bl.1, br.1)) br.2 = some res := by
          simpa [replay, hl, hr] using h
        have hla := ihl tr bl hl
        have hlb := ihr bl.2 br hr
        have hka := ihk (bl.1, br.1) br.2 res hk
        simp only [replay, hla, hlb, hka, Option.bind_some]

/-- Replaying the observations `val` makes returns `val`, having consumed the
whole record: the result is a function of the observations alone.

This is the semantic statement that a reader's result is a function of what it
observed. It cannot speak about physical aliasing, which is why the run-time
check exists. -/
theorem replay_trace (s : Array UInt64) (t : RTree α) :
    replay t (run s t).2 = some (val s t, []) := by
  induction t with
  | pure a => rfl
  | get i k ih => exact ih (s[i]?)
  | size k ih => exact ih s.size
  | fork l r k ihl ihr ihk =>
    have hbl : replay l (run s l).2 = some ((run s l).1, []) := by simpa [val] using ihl
    have hbr : replay r (run s r).2 = some ((run s r).1, []) := by simpa [val] using ihr
    have hbk : replay (k ((run s l).1, (run s r).1))
        (run s (k ((run s l).1, (run s r).1))).2 =
        some ((run s (k ((run s l).1, (run s r).1))).1, []) := by
      simpa [val] using ihk ((run s l).1, (run s r).1)
    have hla := replay_append
      (extra := (run s r).2 ++ (run s (k ((run s l).1, (run s r).1))).2)
      l (run s l).2 ((run s l).1, []) hbl
    have hlb := replay_append
      (extra := (run s (k ((run s l).1, (run s r).1))).2)
      r (run s r).2 ((run s r).1, []) hbr
    simp only [run, val, replay]
    rw [hla]
    simp only [Option.bind_some, List.nil_append]
    rw [hlb]
    simp only [Option.bind_some, List.nil_append]
    rw [hbk]

/-! ## Read phases: threads, steps, and the value they compute

A `Thread` is a read phase being run: a running subtree, or a join waiting for
the two children of a fork. `Step s` relates threads over a fixed array `s`,
and `Eval s t v` relates a thread to the value it computes. -/

/-- A read phase being run: a running subtree at share `q`, or a join waiting
for the two children of a fork, with the continuation the fork will resume. -/
inductive Thread : Type → Type 1 where
  | run {α : Type} (q : Rat) (t : RTree α) : Thread α
  | wait {α : Type} (q : Rat) {β γ : Type} (l : Thread β) (r : Thread γ)
      (k : β × γ → RTree α) : Thread α

/-- The steps of a read phase over the fixed array `s`.

`get` and `size` are the only primitive observations, and they leave `s` alone:
each hands its continuation an `Option UInt64` or a `Nat`. `fork` turns a
running fork into a join over its two children at half the share;
`left`/`right` let either child step, which is what lets the two branches run
in either order or at the same time; `join` resumes the continuation and
requires both children to have terminated. -/
inductive Step (s : Array UInt64) : {α : Type} → Thread α → Thread α → Prop where
  | get {q : Rat} {i : Nat} {k : Option UInt64 → RTree α} :
      Step s (.run q (.get i k)) (.run q (k s[i]?))
  | size {q : Rat} {k : Nat → RTree α} :
      Step s (.run q (.size k)) (.run q (k s.size))
  | fork {q : Rat} {β γ : Type} {l : RTree β} {r : RTree γ} {k : β × γ → RTree α} :
      Step s (.run q (.fork l r k)) (.wait q (.run (q / 2) l) (.run (q / 2) r) k)
  | left {q : Rat} {β γ : Type} {l l' : Thread β} {r : Thread γ} {k : β × γ → RTree α}
      (hstep : Step s l l') : Step s (.wait q l r k) (.wait q l' r k)
  | right {q : Rat} {β γ : Type} {l : Thread β} {r r' : Thread γ} {k : β × γ → RTree α}
      (hstep : Step s r r') : Step s (.wait q l r k) (.wait q l r' k)
  | join {q q₁ q₂ : Rat} {β γ : Type} {b : β} {c : γ} {k : β × γ → RTree α} :
      Step s (.wait q (.run q₁ (.pure b)) (.run q₂ (.pure c)) k) (.run q (k (b, c)))

/-- The reflexive-transitive closure of a read phase's steps: a complete run of
a read phase, of any length, under any interleaving. -/
inductive StepStar (s : Array UInt64) : {α : Type} → Thread α → Thread α → Prop where
  | refl {α : Type} (t : Thread α) : StepStar s t t
  | tail {α : Type} {a b c : Thread α} (h : StepStar s a b) (hstep : Step s b c) :
      StepStar s a c

/-- Relates a thread to what it computes. It is a relation rather than a
function because a thread's termination is what is at stake: `Eval` says the
thread has a value, and `eval_run` shows the sequential denotation is one way
to have it. -/
inductive Eval (s : Array UInt64) : {α : Type} → Thread α → α → Prop where
  | pure {q : Rat} {a : α} : Eval s (.run q (.pure a)) a
  | get {q : Rat} {i : Nat} {k : Option UInt64 → RTree α} {v : α}
      (hstep : Eval s (.run q (k s[i]?)) v) : Eval s (.run q (.get i k)) v
  | size {q : Rat} {k : Nat → RTree α} {v : α}
      (hstep : Eval s (.run q (k s.size)) v) : Eval s (.run q (.size k)) v
  | fork {q : Rat} {β γ : Type} {l : RTree β} {r : RTree γ} {k : β × γ → RTree α}
      {b : β} {c : γ} {v : α}
      (hl : Eval s (.run (q / 2) l) b) (hr : Eval s (.run (q / 2) r) c)
      (hk : Eval s (.run q (k (b, c))) v) : Eval s (.run q (.fork l r k)) v
  | wait {q : Rat} {β γ : Type} {l : Thread β} {r : Thread γ} {k : β × γ → RTree α}
      {b : β} {c : γ} {v : α}
      (hl : Eval s l b) (hr : Eval s r c) (hk : Eval s (.run q (k (b, c))) v) :
      Eval s (.wait q l r k) v

/-- A `get` step hands its continuation exactly `s[i]?`, an `Option UInt64`
detached from the array. -/
theorem step_get {s : Array UInt64} {q : Rat} {i : Nat} {k : Option UInt64 → RTree α}
    {u : Thread α} (h : Step s (.run q (.get i k)) u) : u = .run q (k s[i]?) := by
  cases h; rfl

/-- A `size` step hands its continuation exactly `s.size`, a `Nat`. -/
theorem step_size {s : Array UInt64} {q : Rat} {k : Nat → RTree α} {u : Thread α}
    (h : Step s (.run q (.size k)) u) : u = .run q (k s.size) := by
  cases h; rfl

/-- Every step preserves the value a thread computes. -/
theorem eval_step : ∀ {s : Array UInt64} {α : Type} {t u : Thread α},
    Step s t u → ∀ v, Eval s t v → Eval s u v := by
  intro s α t u h
  induction h with
  | get => intro v hv; cases hv with | get hv => exact hv
  | size => intro v hv; cases hv with | size hv => exact hv
  | fork => intro v hv; cases hv with | fork hb hc hk => exact .wait hb hc hk
  | left hstep ih => intro v hv; cases hv with | wait hl hr hk => exact .wait (ih _ hl) hr hk
  | right hstep ih => intro v hv; cases hv with | wait hl hr hk => exact .wait hl (ih _ hr) hk
  | join => intro v hv; cases hv with
    | wait hl hr hk =>
      cases hl with | pure =>
      cases hr with | pure =>
      exact hk

/-- A thread computes at most one value. -/
theorem eval_unique {s : Array UInt64} :
    ∀ {t : Thread α} {a : α}, Eval s t a → ∀ {b : α}, Eval s t b → a = b := by
  intro t a h1
  induction h1 with
  | pure => intro b h2; cases h2; rfl
  | get hstep ih => intro b h2; cases h2 with | get h2 => exact ih h2
  | size hstep ih => intro b h2; cases h2 with | size h2 => exact ih h2
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

/-- The sequential denotation computes a value the thread has: every complete
run of the read phase computes it. -/
theorem eval_run (s : Array UInt64) : ∀ (t : RTree α) (q : Rat), Eval s (.run q t) (val s t) := by
  intro t
  induction t with
  | pure a => intro q; exact .pure
  | get i k ih => intro q; exact .get (ih (s[i]?) q)
  | size k ih => intro q; exact .size (ih s.size q)
  | fork l r k ihl ihr ihk =>
    intro q
    have h := Eval.fork (ihl (q / 2)) (ihr (q / 2)) (ihk (val s l, val s r) q)
    simpa [val, run] using h

/-- Every step of a run preserves the value the run computes. -/
theorem eval_stepStar {s : Array UInt64} {u v : Thread α} {x : α}
    (h : StepStar s u v) (hu : Eval s u x) : Eval s v x := by
  induction h with
  | refl => exact hu
  | tail _ hstep ih => exact eval_step hstep _ ih

/-- Along a complete run of a read phase, every thread computes the value the
sequential denotation computes: the run's own value is that value, whatever the
interleaving. -/
theorem eval_of_run {s : Array UInt64} {t : RTree α} {t' : Thread α}
    (h : StepStar s (.run 1 t) t') (ha : Eval s t' a) : a = val s t := by
  have hev : Eval s t' (val s t) := eval_stepStar h (eval_run s t 1)
  exact (eval_unique hev ha).symm

/-- A read phase that reaches a finished run computes the sequential
denotation's value, under every interleaving. -/
theorem complete_run_value {s : Array UInt64}
    (h : StepStar s (.run 1 t) (.run 1 (.pure a))) : a = val s t :=
  eval_of_run h .pure

/-! ## Shares

A read phase's fractions are an invariant of the threads rather than a value a
client writes: `WFtree q t` says a read tree is well formed at share `q`, and
`WF q t` says a thread is. The root read phase holds `1`, a fork splits its
share in half, and a join restores the parent's share. `leafSum` counts the
shares of the active leaves; the theorems below say the count is the share,
that no step creates or loses a fraction, and that a positive share makes every
leaf's share positive. -/

/-- The share invariant of a read tree: `get` and `size` run at their share
whatever they observe; a fork gives each child half its share and resumes its
continuation at the parent's share. -/
def WFtree (q : Rat) : RTree α → Prop
  | .pure _ => True
  | .get _ k => ∀ o, WFtree q (k o)
  | .size k => ∀ n, WFtree q (k n)
  | .fork l r k => WFtree (q / 2) l ∧ WFtree (q / 2) r ∧ ∀ p, WFtree q (k p)

/-- The share invariant of a read phase being run. A running subtree is well
formed at its share; a join's children are well formed at half its share and
its continuation at the whole of it. -/
def WF (q : Rat) : Thread α → Prop
  | .run q' t => q = q' ∧ WFtree q t
  | .wait q' l r k => q = q' ∧ WF (q / 2) l ∧ WF (q / 2) r ∧ ∀ p, WFtree q (k p)

/-- The shares of a thread's active leaves: a running subtree is one leaf at its
share, and a join's leaves are its children's. -/
def leafSum : Thread α → Rat
  | .run q _ => q
  | .wait _ l r _ => leafSum l + leafSum r

/-- Every active leaf's share is positive. -/
def sharesPositive : Thread α → Prop
  | .run q _ => 0 < q
  | .wait _ l r _ => sharesPositive l ∧ sharesPositive r

/-- A well-formed thread's leaves sum to its share: forking splits a share and
joining it puts it back, and no share is counted twice. -/
theorem wf_leafSum : ∀ {t : Thread α}, ∀ {q : Rat}, WF q t → leafSum t = q := by
  intro t
  induction t with
  | run q' tree => intro q h; exact h.1.symm
  | wait q' l r k ihl ihr =>
    intro q h
    obtain ⟨_, hl, hr, _⟩ := h
    have h1 := ihl (q := q / 2) hl
    have h2 := ihr (q := q / 2) hr
    show leafSum l + leafSum r = q
    rw [h1, h2]
    grind

/-- A well-formed thread with a positive share has every leaf's share positive,
so a reader running at a positive share can never observe at share zero. -/
theorem wf_sharesPositive : ∀ {t : Thread α}, ∀ {q : Rat}, WF q t → 0 < q →
    sharesPositive t := by
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
theorem wf_step : ∀ {s : Array UInt64} {α : Type} {t u : Thread α},
    Step s t u → ∀ q, WF q t → WF q u := by
  intro s α t u h
  induction h with
  | get => intro q hw; exact ⟨hw.1, hw.2 _⟩
  | size => intro q hw; exact ⟨hw.1, hw.2 _⟩
  | fork => intro q hw; exact ⟨hw.1, ⟨congrArg (· / 2) hw.1, hw.2.1⟩, ⟨congrArg (· / 2) hw.1, hw.2.2.1⟩, hw.2.2.2⟩
  | left hstep ih => intro q hw; exact ⟨hw.1, ih (q / 2) hw.2.1, hw.2.2⟩
  | right hstep ih => intro q hw; exact ⟨hw.1, hw.2.1, ih (q / 2) hw.2.2.1, hw.2.2.2⟩
  | join => intro q hw; exact ⟨hw.1, hw.2.2.2 _⟩

/-- A `wait` node becomes a `run` only by the join step, which requires both
children to have terminated; every other step of a `wait` node yields a `wait`
node. This is why a read phase cannot be short-circuited: the congruence rules
move the join's own subtree, and only a terminated pair lets the continuation
run. -/
theorem wait_step {s : Array UInt64} {q : Rat} {β γ : Type} {l : Thread β}
    {r : Thread γ} {k : β × γ → RTree α} {u : Thread α}
    (h : Step s (.wait q l r k) u) :
    (∃ q' l' r', u = .wait q' l' r' k) ∨
    (∃ (q₁ q₂ : Rat) (b : β) (c : γ),
      l = .run q₁ (.pure b) ∧ r = .run q₂ (.pure c) ∧ u = .run q (k (b, c))) := by
  cases h with
  | left hstep => exact .inl ⟨_, _, _, rfl⟩
  | right hstep => exact .inl ⟨_, _, _, rfl⟩
  | join => exact .inr ⟨_, _, _, _, rfl, rfl, rfl⟩

/-! ## Programs

A program is either `exclusive` — it holds the array, and its writer's
authority is `1` — or `reading`, with a read phase's subtree running and the
writer's authority `0`. `PStep` relates program configurations, and the `set`
rule exists only in the exclusive one, which is what makes a write during a
read phase unrepresentable rather than merely discouraged. -/

/-- A program configuration: `exclusive` holds the array and the tree that is
left to run; `reading` runs a read phase's subtree, with the program to resume
once it terminates. -/
inductive PConf : Type 1 where
  | exclusive {α : Type} (s : Array UInt64) (t : PTree α) : PConf
  | reading {β : Type} (s : Array UInt64) (th : Thread β) (k : β → PTree α) : PConf

/-- The steps of a program. A `set` step exists only in the exclusive
configuration, where the writer's authority is `1`; `enter` starts a read phase
at share `1`; `read` moves the running subtree; `leave` resumes the program,
and only from a thread that is a single finished reader. -/
inductive PStep : PConf → PConf → Prop where
  | set {α : Type} {s : Array UInt64} {i : Nat} {v : UInt64} {k : Bool → PTree α} :
      PStep (.exclusive s (.set i v k))
        (.exclusive (if i < s.size then s.set! i v else s) (k (decide (i < s.size))))
  | enter {α β : Type} {s : Array UInt64} {r : RTree β} {k : β → PTree α} :
      PStep (.exclusive s (.phase r k)) (.reading s (.run 1 r) k)
  | read {β : Type} {s : Array UInt64} {th th' : Thread β} {k : β → PTree α}
      (hstep : Step s th th') : PStep (.reading s th k) (.reading s th' k)
  | leave {β : Type} {s : Array UInt64} {a : β} {k : β → PTree α} :
      PStep (.reading s (.run 1 (.pure a)) k) (.exclusive s (k a))

/-- The share invariant of a program tree: a `set` runs when it is in bounds
whatever the answer; a read phase is well formed at share `1`, the whole state,
and its continuation too. -/
def WFptree : PTree α → Prop
  | .pure _ => True
  | .set _ _ k => ∀ b, WFptree (k b)
  | .phase r k => WFtree 1 r ∧ ∀ a, WFptree (k a)

/-- The share invariant of a program configuration: the tree that is left is
well formed, and while a read phase runs, its thread is well formed at share
`1` and the program to resume is too. Every configuration this relation reaches
from `exclusive` therefore has the whole share accounted for. -/
def WFConf : PConf → Prop
  | .exclusive _ t => WFptree t
  | .reading _ th k => WF 1 th ∧ ∀ a, WFptree (k a)

/-- The writer's authority of a configuration: the whole state while
exclusive, and nothing while a read phase runs. -/
def writerAuthority : PConf → Rat
  | .exclusive _ _ => 1
  | .reading _ th _ => 1 - leafSum th

/-- The share the active readers of a configuration hold. -/
def readerShare : PConf → Rat
  | .exclusive _ _ => 0
  | .reading _ th _ => leafSum th

/-- The sequential denotation of a program tree against an array: the
recursion the shipped executor runs, without the in-place check (which is the
identity in the logic; see `Executor.execP_eq_pval`). A read phase's value is
`val`.

This is the model's evaluator, and it is public: it takes the array from the
caller, so a client can evaluate a tree it has on an array it made itself. It
reaches no session's array — a session's array exists only inside
`Executor.runFresh` — and it is what the theorems above are stated about. -/
def pval (s : Array UInt64) : PTree α → α
  | .pure a => a
  | .set i v k => if i < s.size then pval (s.set! i v) (k true) else pval s (k false)
  | .phase r k => pval s (k (val s r))

/-- From a `reading` configuration a step is either another `read` step or the
`leave` step. The `set` rule's source is `exclusive`, so no write step has a
reading source: a write while a read phase runs is not a step of this
relation. -/
theorem reading_step_is_read_or_leave {s : Array UInt64} {th : Thread β}
    {k : β → PTree α} {c' : PConf} (h : PStep (.reading s th k) c') :
    (∃ th', c' = .reading s th' k) ∨
    (∃ a, th = .run 1 (.pure a) ∧ c' = .exclusive s (k a)) := by
  cases h with
  | read hstep => exact .inl ⟨_, rfl⟩
  | leave => exact .inr ⟨_, rfl, rfl⟩

/-- A read-phase step leaves the store alone: no read primitive writes, so the
array a reader observes cannot change under it. -/
theorem reading_step_store {s s' : Array UInt64} {th th' : Thread β} {k : β → PTree α}
    (h : PStep (.reading s th k) (.reading s' th' k)) : s' = s := by
  cases h with | read _ => rfl

/-- A `set` step's target: the continuation is told whether the index was in
bounds, and the array is the one the write produced exactly then. -/
theorem set_step {s : Array UInt64} {i : Nat} {v : UInt64} {k : Bool → PTree α}
    {c' : PConf} (h : PStep (.exclusive s (.set i v k)) c') :
    c' = .exclusive (if i < s.size then s.set! i v else s) (k (decide (i < s.size))) := by
  cases h; rfl

/-- A `set` step preserves the array's size: an out-of-bounds index leaves the
array alone, and an in-bounds one replaces an element. -/
theorem set_step_size (s : Array UInt64) (i : Nat) (v : UInt64) :
    (if i < s.size then s.set! i v else s).size = s.size := by
  by_cases h : i < s.size
  · simp [h]
  · simp [h]

/-- A well-formed reading configuration's readers hold the whole share —
`leafSum th = 1` — so the writer's authority is `0` while they run. -/
theorem reading_share_is_one {s : Array UInt64} {th : Thread β} {k : β → PTree α}
    (hw : WFConf (.reading s th k)) : leafSum th = 1 := wf_leafSum hw.1

/-- The writer's authority and the readers' shares add up to the whole in every
well-formed configuration: `1` for the writer while exclusive, and all of it
out with the readers — leaving the writer `0` — while a read phase runs. -/
theorem writer_authority_add {c : PConf} (hw : WFConf c) :
    writerAuthority c + readerShare c = 1 := by
  cases c with
  | exclusive s t => show (1 : Rat) + 0 = 1; grind
  | reading s th k =>
    have h1 := reading_share_is_one hw
    show (1 - leafSum th) + leafSum th = 1
    rw [h1]
    grind

/-- Every program step preserves well-formedness, so every configuration
reachable from an exclusive one has the whole share accounted for. -/
theorem pstep_wf {c c' : PConf} (h : PStep c c') (hw : WFConf c) : WFConf c' := by
  cases h with
  | set => exact hw _
  | enter => exact ⟨⟨rfl, hw.1⟩, hw.2⟩
  | read hstep => exact ⟨wf_step hstep 1 hw.1, hw.2⟩
  | leave => exact hw.2 _

end Scidonia.FracPerm.Structured
