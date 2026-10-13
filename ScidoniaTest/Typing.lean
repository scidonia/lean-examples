/-
Checks for `Scidonia.RC.Typing`, from outside the module.

The module fixes the typing `Typed`: the lowering's environment discipline read as a
typing of the source, with a write's subject required to be owned exactly once in its
environment and not borrowed. A proof development has no pre-fix behaviour to observe,
so the checks here meet the typing from outside, on terms and environments a client can
build, and each is paired with a control of the same shape whose failure is pinned. They
are of five kinds:

* **The splits and the readings, evaluated**, as `#guard`s: the usages of the terms the
  checks read and the environments the canonical split functions hand their subterms.
* **The typing's clause applied, and its complement refuted**: the disciplined program
  is typed and its write's subject is read out by `typed_write_owned`, while a program
  that also uses the write's subject, and one whose arm binds it twice, have no typing.
* **The typing narrower than the lowering**: the program the typing refuses is still
  lowered by the canonical strategy --- the lowering supplies its second use with a
  `dup` --- so the typing is a restriction of the lowering's discipline rather than a
  second one, while a disciplined write lowers to itself with no resource instruction.
* **The counterexample to same-environment survival**, as a redex, its step, and the
  contractum typed at the environments the step leaves.
* **Axioms**: each representative theorem's `#print axioms` output is pinned, so a
  proof that acquires an axiom it should not fails the build.
-/
import Scidonia.RC
import Scidonia.RC.Typing

open Scidonia.RC

namespace ScidoniaTest.Typing

set_option synthInstance.maxSize 400

/-! ## The terms the checks read -/

/-- The disciplined program: it binds `0` and writes to a name it uses once. -/
def disciplined : Expr := .lam 0 (.con1 7 (.store (.var 0) 0 (.con0 9)))

/-- A program whose write's subject is also the written value. -/
def duplicated : Expr := .lam 0 (.con1 7 (.store (.var 0) 0 (.var 0)))

/-- The program the typing refuses, lowered: the extra use of `0` is supplied by a
`dup`, which a disciplined write would not need. -/
def duplicatedTarget : Expr := .lam 0 (.dup 0 (.con1 7 (.store (.var 0) 0 (.var 0))))

/-
The disciplined program's lowering is itself: no `dup` and no `drop` is demanded. The
program the typing refuses is still lowered, with a `dup` supplying the second use.
-/
#guard decide (lowerB [] [] disciplined = some disciplined)
#guard decide (lowerB [] [] duplicated = some duplicatedTarget)

/--
error: Expression
  decide (lowerB [] [] disciplined = some (Expr.con0 9))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (lowerB [] [] disciplined = some (.con0 9))

/-
The usages the splits are read from: the disciplined program's store uses its subject
once, the duplicated program's twice.
-/
#guard decide (uses (.store (.var 0) 0 (.con0 9)) = [0])
#guard decide (uses (.store (.var 0) 0 (.var 0)) = [0, 0])

/--
error: Expression
  decide (uses ((Expr.var 0).store 0 (Expr.con0 9)) = [0, 0])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (uses (.store (.var 0) 0 (.con0 9)) = [0, 0])

/-
The environment the write is handed: the store's own usage carries two occurrences of
`0` when the subject is also the value, and one otherwise.
-/
#guard decide (claimEnv [0] (uses (.store (.var 0) 0 (.var 0))) = [0, 0])
#guard decide (claimEnv [0] (uses (.store (.var 0) 0 (.con0 9))) = [0])

/--
error: Expression
  decide (claimEnv [0] (uses ((Expr.var 0).store 0 (Expr.con0 9))) = [0, 0])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (claimEnv [0] (uses (.store (.var 0) 0 (.con0 9))) = [0, 0])

/-! ## The typing applied, and its complement -/

/-- The disciplined program is typed at the empty environments. -/
theorem disciplined_typed : Typed [] [] disciplined := ownedValue_typed

/-- Its write's subject is owned exactly once there and not borrowed, read by the
traversal `typed_write_owned`. -/
theorem disciplined_write_owned : WriteOwned [] [] disciplined :=
  typed_write_owned disciplined_typed

/-- A program whose write's subject is also the written value has no typing. -/
theorem duplicated_no_typing : ¬ Typed [] [] duplicated := dupValue_no_typing

/-- A program whose arm binds the write's subject twice has no typing. -/
theorem arm_duplicated_no_typing : ¬ Typed [] [] dupArm := dupArm_no_typing

/-- The disciplined program's arm binds the subject once and is typed. -/
theorem arm_owned_typed : Typed [] [] ownedArm := ownedArm_typed

/-- The typing is narrower than the lowering: the program the typing refuses is still a
lowering of the canonical strategy, so the typing is the lowering's discipline
restricted and not a second notion. -/
theorem duplicated_lowers : ∃ e', Lower [] [] duplicated e' :=
  lower_total (by decide) (by intro x hx; simp [duplicated, uses] at hx)

/-- A typed term is a term of the source fragment. -/
theorem disciplined_pure : Pure disciplined := typed_pure disciplined_typed

/-! ## The counterexample to preservation at the step's own environments

The typing of a redex does not survive the step at the environments the step starts
from: the redex below is typed at `[]`, `[5, 5]`, and its contractum is typed at
`[]`, `[5]` and not at `[]`, `[5, 5]`. The value restriction a substitution semantics
needs is about the environment's occurrence of the substituted variable --- here `5`
held twice --- and not about the contractum's shape. -/

/-- The redex: it binds `0`, writes to `0`'s cell, and passes the variable `5`. -/
def redex : Expr := .app (.lam 0 (.store (.var 0) 0 (.var 5))) (.var 5)

/-- The contractum the step reaches. -/
def contractum : Expr := .store (.var 5) 0 (.var 5)

/-- The redex is typed at the environments the step starts from: the body's write is
met at the environment `[0, 5]`, where the subject's occurrence is the binder's own, and
the argument is met at `[5, 5]`. -/
theorem redex_typed : Typed [] [5, 5] redex := by
  unfold redex
  refine Typed.app ?_ ?_
  · refine Typed.lam (x := 0) ?_
    refine Typed.store ?_ (by decide) ?_
    · decide
    · exact Typed.var (Or.inl (by decide))
  · exact Typed.var (Or.inl (by decide))

/-- The redex steps to its contractum by the source's `beta` rule. -/
theorem redex_steps : Root redex contractum := by
  unfold redex contractum
  exact Root.beta (Value.var 5)

/-- The contractum is the substitution the step makes. -/
theorem contractum_is_subst : subst 0 (.var 5) (.store (.var 0) 0 (.var 5)) = contractum := rfl

/-- The contractum is not typed at the environments the step starts from: the write's
clause asks for the subject's occurrence to be single, and the environment holds two. -/
theorem contractum_not_typed : ¬ Typed [] [5, 5] contractum := by
  intro h
  unfold contractum at h
  cases h with
  | store hown _ _ => exact absurd hown (by decide)

/-- The contractum is typed once the environment holds the subject's occurrence once. -/
theorem contractum_typed_one : Typed [] [5] contractum := by
  unfold contractum
  refine Typed.store (by decide) (by decide) ?_
  exact Typed.var (Or.inl (by decide))

/-! ## Axioms of representative theorems -/

/--
info: 'Scidonia.RC.typed_write_owned' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms typed_write_owned

/--
info: 'Scidonia.RC.typed_lowers' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms typed_lowers

/--
info: 'Scidonia.RC.typed_pure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms typed_pure

/--
info: 'Scidonia.RC.typed_run_pure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms typed_run_pure

/--
info: 'Scidonia.RC.dupValue_no_typing' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dupValue_no_typing

/--
info: 'Scidonia.RC.dupArm_no_typing' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dupArm_no_typing

/--
info: 'Scidonia.RC.ownedValue_typed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ownedValue_typed

/--
info: 'Scidonia.RC.typed_store_no_root_update' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms typed_store_no_root_update

/--
info: 'ScidoniaTest.Typing.redex_typed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.Typing.redex_typed

/--
info: 'ScidoniaTest.Typing.contractum_not_typed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.Typing.contractum_not_typed

end ScidoniaTest.Typing
