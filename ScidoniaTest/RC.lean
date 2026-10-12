/-
Checks for `Scidonia.RC` from outside the library.

The subject is a calculus rather than a program, so the checks here are of five
kinds:

* **The reduction, evaluated**, as `#guard`s of the evaluator `step?` on small
  hand-written configurations: the beta rule, the binding, the match and the
  write, a step in a subterm, an application whose argument is not a value (which
  steps in the argument rather than at the root), and the configurations the
  calculus leaves stuck — a node in the function position, a free variable there,
  a write whose value is not a value, and a match whose subject is a variable.
  Each guard stands beside a pinned failing control of the same shape, so a guard
  is shown to fire rather than to pass whatever it is given.
* **The substitution, evaluated**: a lambda whose body uses a free variable,
  bound, then applied after that name is rebound, so that the value it resolves to
  is the definition-time one. Its control is the same shape without the
  rebinding, and each is pinned in both directions.
* **The lowering, evaluated**, as `#guard`s of the strategy `lowerB`: the two
  instructions the source does not have (`dup` where an owned occurrence is used
  twice, `drop` where an owned occurrence is not used), the two environments
  telling a double use apart (a borrowed name used twice needs no `dup`, an owned
  one does), a lambda whose binder is used twice, a match whose binder is used
  twice, a write whose subject is duplicated beside its value, and a variable
  neither environment supplies, which the strategy turns away. Each stands beside
  a pinned failing control of the same shape.
* **Negative controls as theorems**: a term that is not in the source fragment,
  the shapes that are never values, and an application shown not to be a value by
  reading off the shapes the canonicity statement admits.
* **The relation and its theorems, applied at those terms**: the target the
  strategy answered is the one the relation gives, any other lowering of the same
  term from the same environments is that one, and every term of the fragment has
  a lowering from the environments that fit it.
* **Axioms**: representative theorems' `#print axioms` output is pinned, so a
  proof that acquires an axiom beyond the standard kernel principles fails the
  build rather than printing a longer list for a reader to notice.

The terms below are hand-written rather than read off a compiled run: this
module's subject is a calculus, and the heaps and programs of the other checks
are not part of it.
-/
import Scidonia.RC

namespace ScidoniaTest.RC

open Scidonia.RC

/-! ## The configurations the checks are read at -/

/-- The identity abstraction `λx. x`. -/
def idTerm : Expr := .lam 0 (.var 0)

/-- The beta rule's configuration `(λx. x) (C 7)`. -/
def betaTerm : Expr := .app idTerm (.con0 7)

/-- A variable in the function position, `x (C 3)`: no rule of the reduction
resolves a free variable, so this configuration has no step. -/
def freeFunTerm : Expr := .app (.var 0) (.con0 3)

/-- The binding `val x = C 3; x`. -/
def bindTerm : Expr := .bind 0 (.con0 3) (.var 0)

/-- The match `match C (C 3) { 5 y → y }`, whose subject is the node it is. -/
def matchTerm : Expr := .matchC (.con1 5 (.con0 3)) 5 [1] (.var 1)

/-- The match `match x { 5 y → y }`, whose subject is still a variable: a subject
that is not a node is stuck, which is the discipline a closed source has. -/
def matchVarTerm : Expr := .matchC (.var 0) 5 [1] (.var 1)

/-- The write `C (C 1) (C 2).1 := C 9`, whose subject is the node it is. -/
def storeTerm : Expr := .store (.con2 5 (.con0 1) (.con0 2)) 1 (.con0 9)

/-- The binding whose bound term is not a value, `val x = (λy. y) (C 4); x`. -/
def subTerm : Expr := .bind 0 (.app idTerm (.con0 4)) (.var 0)

/-- An application whose function is a value and whose argument is not,
`(λx. x) ((λy. y) (C 4))`: the root rule has no redex here, and the step that
this configuration does have is the argument's. -/
def argNotValueTerm : Expr := .app idTerm (.app idTerm (.con0 4))

/-- A node in the function position, `C (C 2)`: the reduction has no rule for it,
because the calculus is untyped and a node is not a function. -/
def nodeAppTerm : Expr := .app (.con0 1) (.con0 2)

/-- A write whose value is not a value, `C 5.1 := (λy. y) (C 3)`: no rule applies,
which is the A-normal shape the source calculus reads. -/
def storeNonValueTerm : Expr := .store (.con0 5) 1 (.app idTerm (.con0 3))

/-- A lambda whose body uses a free variable, bound and then applied after that
name is rebound: `val y = λw. C 1; val x = λz. (y (C 7)); val y = λw. C 2; x (C 3)`.
The substitution resolves `y` when the first binding is reduced, so the
abstraction applied at the end carries the definition-time body and the value
that comes out is `C 1`, not the `C 2` the last binding of `y` names. -/
def captureTerm : Expr :=
  .bind 1 (.lam 2 (.con0 1))
    (.bind 0 (.lam 3 (.app (.var 1) (.con0 7)))
      (.bind 1 (.lam 2 (.con0 2)) (.app (.var 0) (.con0 3))))

/-- The same shape without the rebinding of `y`, so that the value the shape
yields is read once with the rebinding and once without it. -/
def captureControlTerm : Expr :=
  .bind 1 (.lam 2 (.con0 1))
    (.bind 0 (.lam 3 (.app (.var 1) (.con0 7))) (.app (.var 0) (.con0 3)))

/-! ## The reduction, evaluated

Every `#guard` below is answered by a pinned failing control of the same shape,
so the guard is shown to fire rather than to pass whatever it is given. -/

/-
The beta rule: the abstraction applied to the node is its body with the binder
substituted, and the substitution of this body leaves the node itself.
-/
#guard decide (step? betaTerm = some (Expr.con0 7))

/--
error: Expression
  decide (step? betaTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? betaTerm = none)

/-
No rule resolves a free variable: a variable in the function position is a
variable, so the configuration has no step.
-/
#guard decide (step? freeFunTerm = none)

/--
error: Expression
  decide (step? freeFunTerm = some (Expr.con0 3))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? freeFunTerm = some (Expr.con0 3))

/-
The binding: a value bound to a name is the body with the binder substituted.
-/
#guard decide (step? bindTerm = some (Expr.con0 3))

/--
error: Expression
  decide (step? bindTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? bindTerm = none)

/-
The match: the subject is the node, it carries the arm's tag, and the arm's
binder receives its field.
-/
#guard decide (step? matchTerm = some (Expr.con0 3))

/--
error: Expression
  decide (step? matchTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? matchTerm = none)

/-
A subject that is still a variable has no tag, so the match has no step: the
discipline is that a subject reaches the rule as the node a binding substituted
into it.
-/
#guard decide (step? matchVarTerm = none)

/--
error: Expression
  decide (step? matchVarTerm = some (Expr.var 1))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? matchVarTerm = some (Expr.var 1))

/-
The write: the node's slot `1` becomes the written value and the node keeps its
other field. The write is the construct this slice's claim lives in; at the
source it is functional, and whether the target's write updates in place is the
reference count's business, which this slice does not model.
-/
#guard decide
  (step? storeTerm = some (Expr.con2 5 (Expr.con0 1) (Expr.con0 9)))

/--
error: Expression
  decide (step? storeTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? storeTerm = none)

/-
A step in a subterm: the bound term is not a value, so the binding's own rule
does not apply and the step happens inside the bound term.
-/
#guard decide (step? subTerm = some (Expr.bind 0 (Expr.con0 4) (Expr.var 0)))

/--
error: Expression
  decide (step? subTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? subTerm = none)

/-
An application whose argument is not a value: the root rule demands a value
argument, so there is no redex at the root, and the step this configuration has
is the argument's — the configuration is not stuck, which is what the control
beside this guard pins.
-/
#guard decide (step? argNotValueTerm = some (Expr.app idTerm (Expr.con0 4)))

/--
error: Expression
  decide (step? argNotValueTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? argNotValueTerm = none)

/-
Stuck configurations: a node is not a function, and a write's value has to be a
value before the write applies.
-/
#guard decide (step? nodeAppTerm = none)
#guard decide (step? storeNonValueTerm = none)

/--
error: Expression
  decide (step? nodeAppTerm = some (Expr.con0 2))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? nodeAppTerm = some (Expr.con0 2))

/--
error: Expression
  decide (step? storeNonValueTerm = some (Expr.con0 1))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? storeNonValueTerm = some (Expr.con0 1))

/-! ## The substitution, evaluated

A lambda whose body uses a free variable is bound, that name is rebound, and the
lambda is then applied. The substitution resolved the name when the lambda was
bound, so the value the term reaches is the definition-time one. The same shape
without the rebinding reads the same value, which is the control beside it. -/

/-
The capture case reaches the definition-time value `C 1`.
-/
#guard decide (run 24 captureTerm = Expr.con0 1)

/--
error: Expression
  decide (run 24 captureTerm = Expr.con0 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (run 24 captureTerm = Expr.con0 2)

/-
The same shape without the rebinding reaches the same value, so the rebinding is
what the case above turns on rather than the shape alone.
-/
#guard decide (run 24 captureControlTerm = Expr.con0 1)

/--
error: Expression
  decide (run 24 captureControlTerm = Expr.con0 2)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (run 24 captureControlTerm = Expr.con0 2)

/-! ## The lowering, evaluated -/

/-
The two instructions the source does not have, in the positions Figures 5 and 8
put them: a binding whose body uses its name twice is followed by a `dup`, and a
binding whose body does not use its name by a `drop`.
-/
#guard decide
  (lowerB [] [] (.bind 0 (.con0 0) (.app (.var 0) (.var 0))) =
    some (Expr.bind 0 (Expr.con0 0) (Expr.dup 0 (Expr.app (Expr.var 0) (Expr.var 0)))))

/--
error: Expression
  decide (lowerB [] [] (Expr.bind 0 (Expr.con0 0) ((Expr.var 0).app (Expr.var 0))) = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide
  (lowerB [] [] (.bind 0 (.con0 0) (.app (.var 0) (.var 0))) = none)

/-
The same binding with no use at all of the name it introduces.
-/
#guard decide
  (lowerB [] [] (.bind 0 (.con0 0) (.con0 1)) =
    some (Expr.bind 0 (Expr.con0 0) (Expr.drop 0 (Expr.con0 1))))

/--
error: Expression
  decide (lowerB [] [] (Expr.bind 0 (Expr.con0 0) (Expr.con0 1)) = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide
  (lowerB [] [] (.bind 0 (.con0 0) (.con0 1)) = none)

/-
The two environments tell a double use apart: a borrowed name is the context's,
so using it twice needs no instruction, while an owned occurrence used twice has
to be duplicated first.
-/
#guard decide (lowerB [0] [] (.app (.var 0) (.var 0)) = some (Expr.app (Expr.var 0) (Expr.var 0)))

/--
error: Expression
  decide (lowerB [0] [] ((Expr.var 0).app (Expr.var 0)) = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (lowerB [0] [] (.app (.var 0) (.var 0)) = none)

#guard decide
  (lowerB [] [0] (.app (.var 0) (.var 0)) =
    some (Expr.dup 0 (Expr.app (Expr.var 0) (Expr.var 0))))

/--
error: Expression
  decide (lowerB [] [0] ((Expr.var 0).app (Expr.var 0)) = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (lowerB [] [0] (.app (.var 0) (.var 0)) = none)

/-
A lambda whose binder is used twice: the duplication lands inside the
abstraction, because the binder's one occurrence is what the body's two uses
need.
-/
#guard decide
  (lowerB [] [] (.lam 0 (.app (.var 0) (.var 0))) =
    some (Expr.lam 0 (Expr.dup 0 (Expr.app (Expr.var 0) (Expr.var 0)))))

/--
error: Expression
  decide (lowerB [] [] (Expr.lam 0 ((Expr.var 0).app (Expr.var 0))) = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (lowerB [] [] (.lam 0 (.app (.var 0) (.var 0))) = none)

/-
A match whose binder is used twice: the subject is the borrowed occurrence the
environment lends, and the body's two uses of the arm's binder duplicate it.
-/
#guard decide
  (lowerB [0] [] (.matchC (.var 0) 5 [1] (.app (.var 1) (.var 1))) =
    some (Expr.matchC (Expr.var 0) 5 [1] (Expr.dup 1 (Expr.app (Expr.var 1) (Expr.var 1)))))

/--
error: Expression
  decide (lowerB [0] [] ((Expr.var 0).matchC 5 [1] ((Expr.var 1).app (Expr.var 1))) = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide
  (lowerB [0] [] (.matchC (.var 0) 5 [1] (.app (.var 1) (.var 1))) = none)

/-
A match whose subject is a variable neither environment supplies is turned away:
the subject is a subterm of the term, so its occurrences have to be supplied like
any other subterm's.
-/
#guard decide (lowerB [] [] (.matchC (.var 0) 5 [1] (.con0 1)) = none)

/--
error: Expression
  decide (lowerB [] [] ((Expr.var 0).matchC 5 [1] (Expr.con0 1)) = some ((Expr.var 0).matchC 5 [1] (Expr.con0 1)))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide
  (lowerB [] [] (.matchC (.var 0) 5 [1] (.con0 1)) =
    some (Expr.matchC (Expr.var 0) 5 [1] (Expr.con0 1)))

/-
A write whose subject is used twice — once as the node written and once as the
value written: the owned occurrence is duplicated before the write, and the write
itself is left where it was.
-/
#guard decide
  (lowerB [] [0] (.store (.var 0) 0 (.var 0)) =
    some (Expr.dup 0 (Expr.store (Expr.var 0) 0 (Expr.var 0))))

/--
error: Expression
  decide (lowerB [] [0] ((Expr.var 0).store 0 (Expr.var 0)) = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (lowerB [] [0] (.store (.var 0) 0 (.var 0)) = none)

/-
A variable neither environment supplies is not lowered at all.
-/
#guard decide (lowerB [] [] (.var 3) = none)

/--
error: Expression
  decide (lowerB [] [] (Expr.var 3) = some (Expr.var 3))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (lowerB [] [] (.var 3) = some (Expr.var 3))

/-! ## Negative controls

`dup` and `drop` are not source syntax: `Pure` has no rule for either, and the
decidable test of purity agrees, which is what the guards read. -/

/-- `dup x; x` is not a term of the source fragment. -/
theorem dup_not_pure : ¬ Pure (.dup 0 (.var 0)) := not_pure_dup 0 (.var 0)

/-- `drop x; x` is not a term of the source fragment. -/
theorem drop_not_pure : ¬ Pure (.drop 0 (.var 0)) := not_pure_drop 0 (.var 0)

#guard decide (Pure (.dup 0 (.var 0))) == false
#guard decide (Pure (.lam 0 (.app (.var 0) (.var 0)))) == true

/--
error: Expression
  decide (Scidonia.RC.Pure (Expr.dup 0 (Expr.var 0))) == true
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (Pure (.dup 0 (.var 0))) == true

/--
error: Expression
  decide (Scidonia.RC.Pure (Expr.lam 0 ((Expr.var 0).app (Expr.var 0)))) == false
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (Pure (.lam 0 (.app (.var 0) (.var 0)))) == false

/-- An application is never a value. -/
theorem app_not_value : ¬ Value (.app idTerm (.con0 3)) := not_value_app _ _

/-- A write is never a value. -/
theorem store_not_value : ¬ Value (.store (.con0 3) 1 (.con0 3)) := not_value_store _ _ _

/-- No value is an application, read off the shapes the canonicity statement
admits rather than off the non-value lemma: the same fact the control above
states, from the other side. -/
theorem value_canonical_excludes_app (f a : Expr) : ¬ Value (.app f a) := by
  intro h
  rcases value_canonical h with ⟨x, hx⟩ | ⟨x, body, hb⟩ | ⟨c, hc⟩ | ⟨c, a', hr⟩ | ⟨c, a', b', hr⟩
  · simp at hx
  · simp at hb
  · simp at hc
  · simp at hr
  · simp at hr

/-! ## The relation and its theorems, at those terms -/

/-- The evaluator's first step at the beta configuration is a step of the
relation. -/
theorem beta_step : Step betaTerm (Expr.con0 7) := by
  apply step?_sound
  decide

/-- Purity is preserved along the path that step starts: the fragment's own
statement applied at the configuration the guards read back. -/
theorem beta_pure_step : ∃ e', StepStar betaTerm e' ∧ Pure e' := by
  have hpath : StepStar betaTerm (Expr.con0 7) := StepStar.step beta_step (StepStar.refl _)
  exact ⟨_, hpath, pure_steps_pure hpath (by decide)⟩

/-- A write's contractum is a value: the node the guards write into and the value
they write are both values, so the slot update's result is one. -/
theorem store_step_value : Value (Expr.con2 5 (Expr.con0 1) (Expr.con0 9)) :=
  slotUpdate_value (n := .con2 5 (.con0 1) (.con0 2)) (i := 1) (v := .con0 9)
    (Value.con2 (Value.con0 1) (Value.con0 2)) (Value.con0 9) (by decide)

/-- The capture case the guards read reaches the definition-time value: a fact
about the relation, not only about the evaluator. -/
theorem capture_resolves_at_definition_time : StepStar captureTerm (Expr.con0 1) := by
  have h : run 24 captureTerm = Expr.con0 1 := by decide
  rw [← h]
  exact run_stepStar 24 captureTerm

/-- Its control reaches the same value without the rebinding. -/
theorem capture_control_resolves_at_definition_time :
    StepStar captureControlTerm (Expr.con0 1) := by
  have h : run 24 captureControlTerm = Expr.con0 1 := by decide
  rw [← h]
  exact run_stepStar 24 captureControlTerm

/-- The strategy's answer at the binding whose body uses its name twice is a
lowering of the relation. -/
theorem bind_dup_lower :
    Lower [] [] (.bind 0 (.con0 0) (.app (.var 0) (.var 0)))
      (.bind 0 (.con0 0) (.dup 0 (.app (.var 0) (.var 0)))) := by
  apply lowerB_sound
  decide

/-- Any other lowering of that term from those environments is that one: the
determinism theorem at the term the guards read back. -/
theorem bind_dup_unique {e' : Expr}
    (h : Lower [] [] (.bind 0 (.con0 0) (.app (.var 0) (.var 0))) e') :
    e' = .bind 0 (.con0 0) (.dup 0 (.app (.var 0) (.var 0))) :=
  lower_deterministic h bind_dup_lower

/-- The environments that fit `λx. x x`: the abstraction binds the only variable
its body uses, so the empty environments fit it. -/
theorem fits_lam_self : Fits [] [] (.lam 0 (.app (.var 0) (.var 0))) := by
  intro x hx
  simp [uses] at hx

/-- That term has a lowering from the environments that fit it, which is the
totality theorem at the term the guards read back. -/
theorem lam_self_total : ∃ e', Lower [] [] (.lam 0 (.app (.var 0) (.var 0))) e' :=
  lower_total (by decide) fits_lam_self

/-- The environments that fit a term with a free variable hold it: the borrowed
environment supplies the variable. -/
theorem fits_free : Fits [3] [] (.var 3) := by
  intro x hx
  simp [uses] at hx
  exact Or.inr (by simp [hx])

/-- That term has a lowering too, from the environment that lends its variable:
totality is stated for the environments that fit the term, and this is one of
them. -/
theorem free_total : ∃ e', Lower [3] [] (.var 3) e' :=
  lower_total (by decide) fits_free

/-! ## Axioms

Each of these is asserted: the `#guard_msgs` pins the list `#print axioms` emits,
so a proof that acquires another axiom fails the build rather than printing a
longer list. The two principles that appear are the standard ones this
development rests on. -/

/-- info: 'Scidonia.RC.step_deterministic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.step_deterministic

/-- info: 'Scidonia.RC.subst_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.subst_pure

/-- info: 'Scidonia.RC.pure_steps_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.pure_steps_pure

/-- info: 'Scidonia.RC.run_stepStar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.run_stepStar

/-- info: 'Scidonia.RC.lowerB_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.lowerB_sound

/-- info: 'Scidonia.RC.lower_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.lower_total

/-- info: 'Scidonia.RC.lower_deterministic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.lower_deterministic

/-- info: 'ScidoniaTest.RC.dup_not_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.RC.dup_not_pure

/-- info: 'ScidoniaTest.RC.bind_dup_unique' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.RC.bind_dup_unique

/-- info: 'ScidoniaTest.RC.value_canonical_excludes_app' depends on axioms:
[propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.RC.value_canonical_excludes_app

/-- info: 'ScidoniaTest.RC.beta_pure_step' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.RC.beta_pure_step

/-- info: 'ScidoniaTest.RC.capture_resolves_at_definition_time' depends on
axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.RC.capture_resolves_at_definition_time

end ScidoniaTest.RC
