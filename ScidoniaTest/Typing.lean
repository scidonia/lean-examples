/-
Checks for `Scidonia.RC.Typing`, from outside the module.

The module fixes the typing `Typed`: the lowering's environment discipline read as a
typing of the source, with a write's subject required to be owned exactly once in its
environment and not borrowed, and with two conditions on the name a subject carries ---
a name a rule binds is used exactly once in its scope when its body writes it, and it is
introduced for a construction of the program rather than another name. A proof
development has no pre-fix behaviour to observe, so the checks here meet the typing from
outside, on terms and environments a client can build, and each is paired with a control
of the same shape whose failure is pinned. They are of seven kinds:

* **The splits and the readings, evaluated**, as `#guard`s: the usages of the terms the
  checks read, the environments the canonical split functions hand their subterms, and
  the traversals the name conditions read (`writes`, `BuiltB`, `vars`, `binds`).
* **The typing's clause applied, and its complement refuted**: the disciplined program
  is typed and its write's subject is read out by `typed_write_owned`, while a program
  that also uses the write's subject, and one whose arm binds it twice, have no typing.
* **The name conditions applied, and their complements refuted**: the disciplined
  programs carry `typed_write_linear` and `typed_write_built`, while the program whose
  write's subject is used in a sibling position and the one that binds the written name
  to another name have no typing --- and the counterpart of each is typed.
* **The typing narrower than the lowering**: the program the typing refuses is still
  lowered by the canonical strategy --- the lowering supplies its second use with a
  `dup` --- so the typing is a restriction of the lowering's discipline rather than a
  second one, while a disciplined write lowers to itself with no resource instruction.
* **The counterexample to same-environment survival**, as a redex, its step, and the
  contractum typed at the environments the step leaves, together with the name the
  body mentions twice, which is what the substitution lemma's restriction excludes.
* **The substitution lemma applied**: a typed node whose free name is the substituted
  name's image is typed at the renamed environment, so the lemma produces typings and
  not only refusals.
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

/-- The program whose write's subject is also used in a sibling position: the store's own
occurrence is the subject's, so the write's clause is met and the program holds the cell
twice. -/
def sibling : Expr := .lam 0 (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.var 0)))

/-- The same program with the sibling's second reference replaced by a node. -/
def siblingOwned : Expr := .lam 0 (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.con0 10)))

/-- A program that binds the written name to another name. -/
def alias : Expr := .bind 0 (.var 1) (.store (.var 0) 0 (.con0 9))

/-- The same program with the binding a construction. -/
def built : Expr := .bind 0 (.con1 5 (.con0 5)) (.store (.var 0) 0 (.con0 9))

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
once, the duplicated program's twice, and the sibling program's store once while the
program mentions the name twice.
-/
#guard decide (uses (.store (.var 0) 0 (.con0 9)) = [0])
#guard decide (uses (.store (.var 0) 0 (.var 0)) = [0, 0])
#guard decide (uses (.con2 8 (.store (.var 0) 0 (.con0 9)) (.var 0)) = [0, 0])

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

/-! ## The traversals the name conditions read -/

/-
A write is read at its subject: true where the subject is the free variable asked about,
false under a binder of that name, and true where the name is used beside the write.
-/
#guard writes 0 (.store (.var 0) 0 (.con0 9))
#guard !writes 1 (.store (.var 0) 0 (.con0 9))
#guard !writes 0 (.lam 0 (.store (.var 0) 0 (.con0 9)))
#guard writes 0 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.con0 10))
#guard !writes 0 (.con2 8 (.con0 9) (.con0 10))

/--
error: Expression
  decide (writes 0 (Expr.con2 8 (Expr.con0 9) (Expr.con0 10)) = true)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (writes 0 (.con2 8 (.con0 9) (.con0 10)) = true)

/-
A construction is a node, and a name is none; `vars` collects the names a term mentions
and `binds` the names it binds.
-/
#guard BuiltB (.con1 5 (.con0 5))
#guard !BuiltB (.var 1)
#guard decide (vars (.store (.var 0) 0 (.var 0)) = [0, 0])
#guard decide (binds 0 (.lam 0 (.var 0)) = true)
#guard decide (binds 0 (.con1 7 (.var 1)) = false)

/--
error: Expression
  decide (vars ((Expr.var 0).store 0 (Expr.con0 9)) = [0, 0])
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (vars (.store (.var 0) 0 (.con0 9)) = [0, 0])

/-
The sibling program's body writes `0` and uses it twice, the counterpart's body writes
`0` and uses it once: the count the first name condition reads.
-/
#guard writes 0 (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.var 0)))
#guard decide ((uses (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.var 0)))).count 0 = 2)
#guard decide ((uses (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.con0 10)))).count 0 = 1)

/--
error: Expression
  decide (List.count 0 (uses (Expr.con1 7 (Expr.con2 8 ((Expr.var 0).store 0 (Expr.con0 9)) (Expr.var 0)))) = 1)
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide ((uses (.con1 7 (.con2 8 (.store (.var 0) 0 (.con0 9)) (.var 0)))).count 0 = 1)

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

/-! ## The name conditions applied, and their complements -/

/-- The disciplined program carries the first name condition: its binding rule's body
writes the name it binds and uses it once. -/
theorem disciplined_linear : WriteLinear disciplined := typed_write_linear disciplined_typed

/-- The disciplined program carries the second name condition. -/
theorem disciplined_built : WriteBuilt disciplined := typed_write_built disciplined_typed

/-- The disciplined program's write's subject is used exactly once in its scope, read by
the abstraction rule's own reading of the first name condition. -/
theorem disciplined_write_linear :
    (uses (.con1 7 (.store (.var 0) 0 (.con0 9)))).count 0 = 1 :=
  typed_lam_written_linear disciplined_typed (by decide)

/-- The program that uses the write's subject in a sibling position has no typing: the
body writes `0` and uses it twice, so the first name condition refuses it. The store's
own clause is met --- the sibling's use is not counted at the store --- which is why the
store's own environment alone cannot refuse it. -/
theorem sibling_no_typing : ¬ Typed [] [] sibling := sibling_use_no_typing

/-- The counterpart of the refutation above: the program writes the cell `0` names and
does not use `0` elsewhere, so it is typed. The derivation is given here from the rules,
so the counterpart is not read off the module's own term. -/
theorem sibling_owned_typed : Typed [] [] siblingOwned := by
  unfold siblingOwned
  refine Typed.lam (x := 0) (by decide) ?_
  refine Typed.con1 ?_
  refine Typed.con2 ?_ ?_
  · refine Typed.store (by decide) (by decide) ?_
    exact Typed.con0
  · exact Typed.con0

/-- A program that binds a written name to another name has no typing, at every
environment: the binding rule's second name condition asks the bound term to be a
construction, and a name is none. -/
theorem alias_no_typing : ¬ Typed [] [] alias := by
  unfold alias
  exact alias_bind_no_typing

/-- The counterpart of the refutation above: the same program with the binding a
construction is typed, with the derivation given here from the rules. -/
theorem built_typed : Typed [] [] built := by
  unfold built
  refine Typed.bind (x := 0) (by decide) (by intro _; rfl) (Typed.con1 Typed.con0) ?_
  refine Typed.store (by decide) (by decide) ?_
  exact Typed.con0

/-- The same refutation at an environment that supplies the bound name, so the
refutation is the name condition and not the environment: the program is refused
wherever it is read. -/
theorem alias_no_typing_at_env : ¬ Typed [] [1] alias := by
  unfold alias
  exact alias_bind_no_typing

/-- A written name bound by a binding is bound to a construction and used exactly once
in that binding's body: the cell is the term's own, and the term holds it once. -/
theorem built_written_own :
    BuiltB (.con1 5 (.con0 5)) = true ∧ (uses (.store (.var 0) 0 (.con0 9))).count 0 = 1 :=
  typed_bind_written_own built_typed (by decide)

/-- The same reading at an arm's binder: the written name is matched out of a
construction and used exactly once in the arm's body. -/
theorem arm_written_own :
    BuiltB (.con1 5 (.con0 5)) = true ∧ (uses (.store (.var 0) 0 (.con0 9))).count 0 = 1 :=
  typed_arm_written_own ownedArm_typed (by decide) (by decide)

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
  · refine Typed.lam (x := 0) (by decide) ?_
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

/-- The redex's body mentions `5` twice, so the substitution lemma's freshness
hypothesis is what excludes the redex: the same-environment statement is not what fails,
the restriction is. -/
theorem redex_body_mentions : ¬ (5 ∉ vars (.store (.var 0) 0 (.var 5))) := by decide

/-- The redex's body writes `0` and uses it once, so the first name condition is met at
the redex: what the redex lacks is the substitute's freshness and not the name
condition. -/
theorem redex_body_linear : (uses (.store (.var 0) 0 (.var 5))).count 0 = 1 := by decide

/-! ## The substitution lemma applied -/

/-- The substitution lemma applied to a concrete term: the name `0`'s occurrence is the
image's, and the typing is read at the environment that holds it. -/
theorem subst_applied : Typed [] [5] (Expr.con1 3 (.var 5)) :=
  subst_typed_var (Δ := []) (Γ := [0]) (x := 0) (y := 5) (.con1 3 (.var 0))
    (Typed.con1 (Typed.var (Or.inl (by decide))))
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The same application read the other way: the environments the lemma names are the
mapped ones, so the terms the environments hold are the renamed occurrences. -/
theorem subst_applied_env :
    List.map (rename 0 5) ([] : Occs) = [] ∧ List.map (rename 0 5) ([0] : Occs) = [5] :=
  ⟨rfl, rfl⟩

/-- The lemma's conclusion at the redex's own environments is what the same-environment
statement cannot give: the redex's argument environment holds `5` twice, and the
contractum is refused there. -/
theorem redex_subst_env : ¬ Typed [] (List.map (rename 0 5) ([5, 5] : Occs)) contractum := by
  intro h
  unfold contractum at h
  cases h with
  | store hown _ _ => exact absurd hown (by decide)

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
info: 'Scidonia.RC.typed_write_linear' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms typed_write_linear

/--
info: 'Scidonia.RC.typed_write_built' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms typed_write_built

/--
info: 'Scidonia.RC.sibling_use_no_typing' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sibling_use_no_typing

/--
info: 'Scidonia.RC.alias_bind_no_typing' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms alias_bind_no_typing

/--
info: 'Scidonia.RC.subst_typed_var' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms subst_typed_var

/--
info: 'Scidonia.RC.subst_typed_redex' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms subst_typed_redex

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
