/-
Checks for `Scidonia.RC` from outside the library.

The subject is a calculus rather than a program, so the checks here are of five
kinds:

* **The reduction, evaluated**, as `#guard`s of the evaluator `step?` on small
  hand-written configurations: the beta rule, the beta rule reached through the
  environment, the binding, the match and the write, a step in a subterm, and two
  configurations the calculus leaves stuck — one because an application's
  function is a node, one because a write's value is not a value. Each guard
  stands beside a pinned failing control of the same shape, so a guard is shown
  to fire rather than to pass whatever it is given.
* **The lowering, evaluated**, as `#guard`s of the strategy `lowerB`: the two
  instructions the source does not have (`dup` where an owned occurrence is used
  twice, `drop` where an owned occurrence is not used), the two environments
  telling a double use apart (a borrowed name used twice needs no `dup`, an owned
  one does), a lambda whose binder is used twice, a match whose binder is used
  twice, a write whose target is duplicated beside its value, and a variable
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

/-- The environment binding the variable `0` to the identity abstraction. -/
def idEnv : Env := [(0, idTerm)]

/-- The environment's function position, `x (C 3)`, where `x` names the
abstraction the environment binds. -/
def betaVarTerm : Expr := .app (.var 0) (.con0 3)

/-- The binding `val x = C 3; x`. -/
def bindTerm : Expr := .bind 0 (.con0 3) (.var 0)

/-- The environment binding the variable `0` to the unary node `C (C 3)`. -/
def nodeEnv : Env := [(0, .con1 5 (.con0 3))]

/-- The match `match x { 5 y → y }` on the node the environment binds. -/
def matchTerm : Expr := .matchC 0 5 [1] (.var 1)

/-- The environment binding the variable `0` to the binary node `C (C 1) (C 2)`. -/
def pairEnv : Env := [(0, .con2 5 (.con0 1) (.con0 2))]

/-- The write `x.1 := C 9` on the node the environment binds. -/
def storeTerm : Expr := .store 0 1 (.con0 9)

/-- The binding whose bound term is not a value, `val x = (λy. y) (C 4); x`. -/
def subTerm : Expr := .bind 0 (.app idTerm (.con0 4)) (.var 0)

/-- A node in the function position, `C (C 2)`: the reduction has no rule for it,
because the calculus is untyped and a node is not a function. -/
def nodeAppTerm : Expr := .app (.con0 1) (.con0 2)

/-- A write whose value is not a value, `x.1 := (λy. y) (C 3)`: the reduction has
no rule for it either, which is the A-normal shape the source calculus reads. -/
def storeNonValueTerm : Expr := .store 0 1 (.app idTerm (.con0 3))

/-! ## The reduction, evaluated

Every `#guard` below is answered by a pinned failing control of the same shape,
so the guard is shown to fire rather than to pass whatever it is given. -/

/-
The beta rule: the abstraction applied to the node is its body under the
environment the node extends.
-/
#guard decide (step? [] betaTerm = some ([(0, Expr.con0 7)], Expr.var 0))

/--
error: Expression
  decide (step? [] betaTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? [] betaTerm = none)

/-
The same rule reached through the environment: the function position names an
abstraction the environment binds.
-/
#guard decide (step? idEnv betaVarTerm = some ((0, Expr.con0 3) :: idEnv, Expr.var 0))

/--
error: Expression
  decide (step? idEnv betaVarTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? idEnv betaVarTerm = none)

/-
The binding: a value bound to a name is the body under the environment the
binding extends.
-/
#guard decide (step? [] bindTerm = some ([(0, Expr.con0 3)], Expr.var 0))

/--
error: Expression
  decide (step? [] bindTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? [] bindTerm = none)

/-
The match: the node the environment binds carries the arm's tag, so the arm's
binder receives its field.
-/
#guard decide (step? nodeEnv matchTerm = some ((1, Expr.con0 3) :: nodeEnv, Expr.var 1))

/--
error: Expression
  decide (step? nodeEnv matchTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? nodeEnv matchTerm = none)

/-
The write: the node's slot `1` becomes the written value and the node keeps its
other field. The write is the construct this slice's claim lives in; at the
source it is functional, and whether the target's write updates in place is the
reference count's business, which this slice does not model.
-/
#guard decide
  (step? pairEnv storeTerm = some (pairEnv, Expr.con2 5 (Expr.con0 1) (Expr.con0 9)))

/--
error: Expression
  decide (step? pairEnv storeTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? pairEnv storeTerm = none)

/-
A step in a subterm: the bound term is not a value, so the binding's own rule
does not apply and the step happens inside the bound term.
-/
#guard decide
  (step? [] subTerm = some ([(0, Expr.con0 4)], Expr.bind 0 (Expr.var 0) (Expr.var 0)))

/--
error: Expression
  decide (step? [] subTerm = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? [] subTerm = none)

/-
Stuck configurations: a node is not a function, and a write's value has to be a
value before the write applies.
-/
#guard decide (step? [] nodeAppTerm = none)
#guard decide (step? pairEnv storeNonValueTerm = none)

/--
error: Expression
  decide (step? [] nodeAppTerm = some (pairEnv, Expr.con0 3))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? [] nodeAppTerm = some (pairEnv, Expr.con0 3))

/--
error: Expression
  decide (step? pairEnv storeNonValueTerm = some (pairEnv, Expr.con0 1))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (step? pairEnv storeNonValueTerm = some (pairEnv, Expr.con0 1))

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
A match whose binder is used twice: the arm binds the matched node's field, and
the body's two uses of it duplicate it. The scrutinee is the borrowed occurrence
the environment lends.
-/
#guard decide
  (lowerB [0] [] (.matchC 0 5 [1] (.app (.var 1) (.var 1))) =
    some (Expr.matchC 0 5 [1] (Expr.dup 1 (Expr.app (Expr.var 1) (Expr.var 1)))))

/--
error: Expression
  decide (lowerB [0] [] (Expr.matchC 0 5 [1] ((Expr.var 1).app (Expr.var 1))) = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (lowerB [0] [] (.matchC 0 5 [1] (.app (.var 1) (.var 1))) = none)

/-
A write whose target is used twice — once as the node written and once as the
value written: the owned occurrence is duplicated before the write, and the write
itself is left where it was.
-/
#guard decide
  (lowerB [] [0] (.store 0 0 (.var 0)) = some (Expr.dup 0 (Expr.store 0 0 (Expr.var 0))))

/--
error: Expression
  decide (lowerB [] [0] (Expr.store 0 0 (Expr.var 0)) = none)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (lowerB [] [0] (.store 0 0 (.var 0)) = none)

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
theorem store_not_value : ¬ Value (.store 0 1 (.con0 3)) := not_value_store _ _ _

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
theorem beta_step : Step [] betaTerm ([(0, Expr.con0 7)] : Env) (Expr.var 0) := by
  apply step?_sound
  decide

/-- Purity is preserved along the path that step starts: the fragment's own
statement applied at the configuration the guards read back, with the empty
environment, which binds no value and so is pure. -/
theorem beta_pure_step : ∃ ρ' e', StepStar [] betaTerm ρ' e' ∧ Pure e' := by
  have hpath : StepStar [] betaTerm [(0, Expr.con0 7)] (Expr.var 0) :=
    StepStar.step beta_step (StepStar.refl _ _)
  exact ⟨_, _, hpath, (pure_steps_pure hpath (by decide) pureEnv_nil).1⟩

/-- A write's contractum is a value: the node the guards bind and the value they
write are both values, so the slot update's result is one. -/
theorem store_step_value : Value (Expr.con2 5 (Expr.con0 1) (Expr.con0 9)) :=
  slotUpdate_value (n := .con2 5 (.con0 1) (.con0 2)) (i := 1) (v := .con0 9)
    (Value.con2 (Value.con0 1) (Value.con0 2)) (Value.con0 9) (by decide)

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
longer list. The three principles that appear are the standard ones this
development rests on. -/

/-- info: 'Scidonia.RC.step_deterministic' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.step_deterministic

/-- info: 'Scidonia.RC.pure_steps_pure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.pure_steps_pure

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

end ScidoniaTest.RC
