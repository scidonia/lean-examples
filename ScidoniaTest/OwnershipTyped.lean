/-
Checks for `Scidonia.RC.OwnershipTyped` from outside the library.

The subject is a discipline over a calculus rather than a program, and the checks
here are of seven kinds:

* **The quotation, evaluated**, as `#guard`s of `unquoteSlot` on the quotations
  of `empty`, `full 7` and a payload of thirty decimal digits, together with the
  two laws of the correspondence with the existing `Slot` isomorphism —
  `quoteElSlot_encode` and `quoteElSlot_decode` — read at those slots, and the
  round trips of the existing `Slot.encode`/`decode`. Each guard stands beside a
  pinned failing control of the same shape, so a guard is shown to fire rather
  than to pass whatever it is given.
* **The witnesses, evaluated and proved**: a read–write–read pair that reads a
  cell's slot, writes through the owner and reads the new cell, a two-read
  unchanged-cell pair, and a shape change whose payload
  is an arbitrary natural. Each is admitted, evaluated by the sealed runner,
  reached by the *copying* `RC.StepStar` relation of the existing calculus, and
  the two are the same value by `evalArray_sound`.
* **The refusals, and their paired controls**: a theorem `¬ Own …` for a specific
  expression of each shape the rules cannot admit, beside the same-purpose
  expression they do admit and its evaluated value. No refusal is merely stuck
  because the shape violates A-normal form; each is an inversion of the rules.
* **The omissions, by inversion**: a theorem that there is no rule for an
  abstraction, an application, a `dup` or a `drop`.
* **The totality, quotation and `IO` statements applied** at the witnesses.
* **The sealing**: a `#guard_msgs` around the name of the sealed interpreter,
  which a client cannot write, beside affirmative `#check`s of the public
  evaluation and runner, and a `#guard_msgs` pinning that a client cannot hand
  the runner an array.
* **Axioms**: each representative theorem's `#print axioms` output is pinned, so
  a proof that acquires an axiom fails the build rather than printing a longer
  list for a reader to notice.
-/
import Scidonia.RC

open Scidonia.RC
open Scidonia.RC.OwnershipTyped
open Scidonia.FracPerm.StateVar (Slot encode decode)

namespace ScidoniaTest.OwnershipTyped

/-! ## The quotation, evaluated -/

/-
The round trip at the empty slot, at `full 7` and at a payload of thirty decimal
digits: decoding a quotation is the slot it quotes, whatever the payload's size.
-/
#guard decide (unquoteSlot (quoteSlot Slot.empty) = some Slot.empty)
#guard decide (unquoteSlot (quoteSlot (Slot.full 7)) = some (Slot.full 7))
#guard decide (unquoteSlot (quoteSlot (Slot.full (10 ^ 30))) = some (Slot.full (10 ^ 30)))

/--
error: Expression
  decide (unquoteSlot (quoteSlot Slot.empty) = some (Slot.full 7))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (unquoteSlot (quoteSlot Slot.empty) = some (Slot.full 7))

/-- The round trip is a theorem at every slot, not only at the evaluated ones. -/
theorem unquote_quote_all (s : Slot) : unquoteSlot (quoteSlot s) = some s :=
  unquoteSlot_quoteSlot s

/-- The quotation is injective: two slots with the same quotation are the same
slot, at every payload. -/
theorem quote_injective_all {s t : Slot} (h : quoteSlot s = quoteSlot t) : s = t :=
  quoteSlot_injective h

/-
The correspondence with the existing slot isomorphism, at a payload of thirty
decimal digits: quoting an encoded slot is quoting the slot, and quoting a
decoded element is quoting the element. Both are stated for every slot and every
element, and evaluated here.
-/
#guard decide
  (quoteElSlot (encode (Slot.full (10 ^ 30))) = quoteSlot (Slot.full (10 ^ 30)))

#guard decide
  (quoteSlot (decode (Sum.inr (10 ^ 30))) = quoteElSlot (Sum.inr (10 ^ 30)))

/--
error: Expression
  decide (quoteElSlot (encode (Slot.full 7)) = quoteSlot (Slot.full 9))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide (quoteElSlot (encode (Slot.full 7)) = quoteSlot (Slot.full 9))

/-- The quotation of a slot's encoding is the quotation of the slot, at every
slot, through the existing `Slot.decode_encode`: the round trip through the
isomorphism and the fragment's quotation agree. -/
theorem quote_el_encode_all (s : Slot) : quoteElSlot (encode s) = quoteSlot s :=
  quoteElSlot_encode s

/-- Decoding the quotation of an encoding is the slot, at every slot. -/
theorem unquote_el_encode_all (s : Slot) : unquoteSlot (quoteElSlot (encode s)) = some s :=
  unquoteSlot_quoteElSlot_encode s

/-! ## The witnesses

The read–write–read witness: bind the root of `full 7`, read its slot to `1`, write
`quoteSlot (full 9)` through the same owner, read the new cell to `3`, and return
the pair of the two detached observations. -/

/-- The context holding the owner `0` as a cell. -/
abbrev Γ₁ : TyEnv := TyEnv.empty.extend 0 .cell

/-- `Γ₁` with the first read's slot observation bound to `1`. -/
abbrev Γ₂ : TyEnv := Γ₁.extend 1 (.obs slotObs)

/-- `Γ₂` with the hand-off's cell bound to `2`. -/
abbrev Γ₃ : TyEnv := Γ₂.extend 2 .cell

/-- `Γ₃` with the second read's slot observation bound to `3`. -/
abbrev Γ₄ : TyEnv := Γ₃.extend 3 (.obs slotObs)

/-- The read–write–read witness: bind the root of `full 7`, read it to `1`,
write `full 9` through the owner into a fresh handle `2`, read that to `3`, and
return the pair of the two detached observations. -/
def witness : Expr :=
  .bind 0 (root (.full 7))
    (.matchC (.var 0) rootTag [1]
      (.bind 2 (.store (.var 0) 0 (quoteSlot (.full 9)))
        (.matchC (.var 2) rootTag [3] (.con2 pairTag (.var 1) (.var 3)))))

/-- The value both evaluations of the witness reach: `pair (full 7) (full 9)`,
the old and the new slot. -/
def witnessValue : Expr := .con2 pairTag (quoteSlot (.full 7)) (quoteSlot (.full 9))

/-- The witness is admitted, built from the rules' own accepted shapes: the root
construction, the read, the write, and the pair of two detached observations. -/
theorem witness_own :
    Own (TyEnv.empty : TyEnv) .none witness (.obs (.pair slotObs slotObs)) := by
  unfold witness
  refine Own.cellBind 0 (root (.full 7)) _ (Own.fresh (Obs.full 7)) (by decide) ?_
  refine Own.read 0 1 _ (by decide) (by decide) ?_
  refine Own.cellBind 2 (.store (.var 0) 0 (quoteSlot (.full 9))) _
    (Own.write 0 (by decide) (Obs.full 9)) (by decide) ?_
  refine Own.read 2 3 _ (by decide) (by decide) ?_
  exact Own.obs (Obs.pair (Obs.var 1 (by decide) Fragment.slot)
    (Obs.var 3 (by decide) Fragment.slot))

/-- The copying side of the witness: the existing reduction reaches
`pair (full 7) (full 9)`. -/
theorem witness_run : run 64 witness = witnessValue := by decide

/-- The same, as a statement about the existing step relation rather than about
the evaluator: the copying λPure reduction reaches that value. -/
theorem witness_stepStar : StepStar witness witnessValue := by
  rw [← witness_run]
  exact run_stepStar 64 witness

/-- The witness is a value. -/
theorem witnessValue_value : Value witnessValue := by decide

/-
The witness, evaluated by the sealed runner, and the agreement: the direct side
reaches the same value the copying side's `StepStar` does.
-/
#guard decide (evalArray witness = some witnessValue)

/--
error: Expression
  decide (evalArray witness = some (Expr.con2 pairTag (quoteSlot (Slot.full 7)) (quoteSlot (Slot.full 7))))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide
  (evalArray witness = some (.con2 pairTag (quoteSlot (.full 7)) (quoteSlot (.full 7))))

/-- The agreement applied at the witness: the sealed runner's value is the value
the copying reduction reaches, through the *existing* `StepStar`. -/
theorem witness_agreement : evalArray witness = some witnessValue :=
  evalArray_sound witness_own (by decide) witness_stepStar (by decide)

/-- The quotation lemma applied at the witness: its result carries no protected
root node. -/
theorem witness_no_root : hasRoot witnessValue = false :=
  evalArray_no_root witness_own witness_agreement

/-- The totality applied at the witness: the copying reduction reaches a value
and the runner reaches that value. -/
theorem witness_total :
    StepStar witness witnessValue ∧ Value witnessValue ∧
      evalArray witness = some witnessValue := by
  obtain ⟨v, hstep, hval, heval⟩ :=
    evalArray_total witness_own (by decide)
  have hveq : v = witnessValue :=
    (stepStar_value_unique witness_stepStar (by decide) hstep hval).symm
  rw [hveq] at hstep hval heval
  exact ⟨hstep, hval, heval⟩

/-- The `IO` equation applied at the witness: the runner's description is the
`pure` return of that value. -/
theorem witness_io :
    runFresh witness witness_own = pure witnessValue :=
  runFresh_eq_pure witness_own (by decide) witness_stepStar (by decide)

/-- The two-read unchanged-cell witness: read the cell twice without writing
between the reads. -/
def twoReadWitness : Expr :=
  .bind 0 (root (.full 7))
    (.matchC (.var 0) rootTag [1]
      (.matchC (.var 0) rootTag [3] (.con2 pairTag (.var 1) (.var 3))))

/-- Two reads of an unchanged cell agree: both observations are the same slot. -/
def twoReadValue : Expr := .con2 pairTag (quoteSlot (.full 7)) (quoteSlot (.full 7))

/-- The two-read witness is admitted. -/
theorem twoRead_own :
    Own (TyEnv.empty : TyEnv) .none twoReadWitness (.obs (.pair slotObs slotObs)) := by
  unfold twoReadWitness
  refine Own.cellBind 0 (root (.full 7)) _ (Own.fresh (Obs.full 7)) (by decide) ?_
  refine Own.read 0 1 _ (by decide) (by decide) ?_
  refine Own.read 0 3 _ (by decide) (by decide) ?_
  exact Own.obs (Obs.pair (Obs.var 1 (by decide) Fragment.slot)
    (Obs.var 3 (by decide) Fragment.slot))

/-- The copying side of the two-read witness. -/
theorem twoRead_stepStar : StepStar twoReadWitness twoReadValue := by
  rw [← show run 64 twoReadWitness = twoReadValue from by decide]
  exact run_stepStar 64 twoReadWitness

/-- The two reads agree, by the agreement theorem. -/
theorem twoRead_agreement : evalArray twoReadWitness = some twoReadValue :=
  evalArray_sound twoRead_own (by decide) twoRead_stepStar (by decide)

#guard decide (evalArray twoReadWitness = some twoReadValue)

/-- The shape change `empty → full n → empty` on one cell, with a payload of an
arbitrary size: the root of the empty slot, a write of `full n`, a read of the
new cell, a write of the empty slot through a fresh handle, a read of that, and
the pair of the last two observations. -/
def shapeWitness (n : Nat) : Expr :=
  .bind 0 (root .empty)
    (.matchC (.var 0) rootTag [1]
      (.bind 2 (.store (.var 0) 0 (quoteSlot (.full n)))
        (.matchC (.var 2) rootTag [3]
          (.bind 4 (.store (.var 2) 0 (quoteSlot .empty))
            (.matchC (.var 4) rootTag [5]
              (.con2 pairTag (.var 3) (.var 5)))))))

/-- The value the shape change reaches: `pair (full n) empty`. -/
def shapeValue (n : Nat) : Expr :=
  .con2 pairTag (quoteSlot (.full n)) (quoteSlot .empty)

/-- The shape change is admitted at an arbitrary payload. -/
theorem shape_own (n : Nat) :
    Own (TyEnv.empty : TyEnv) .none (shapeWitness n) (.obs (.pair slotObs slotObs)) := by
  unfold shapeWitness
  refine Own.cellBind 0 (root .empty) _ (Own.fresh Obs.empty) (by decide) ?_
  refine Own.read 0 1 _ (by decide) (by decide) ?_
  refine Own.cellBind 2 (.store (.var 0) 0 (quoteSlot (.full n))) _
    (Own.write 0 (by decide) (Obs.full n)) (by decide) ?_
  refine Own.read 2 3 _ (by decide) (by decide) ?_
  refine Own.cellBind 4 (.store (.var 2) 0 (quoteSlot .empty)) _
    (Own.write 2 (by decide) Obs.empty) (by decide) ?_
  refine Own.read 4 5 _ (by decide) (by decide) ?_
  exact Own.obs (Obs.pair (Obs.var 3 (by decide) Fragment.slot)
    (Obs.var 5 (by decide) Fragment.slot))

/-- The copying side of the shape change, at an arbitrary payload: the reduction
carries the payload and never inspects it. -/
theorem shape_stepStar (n : Nat) : StepStar (shapeWitness n) (shapeValue n) := by
  rw [← show run 64 (shapeWitness n) = shapeValue n from by rfl]
  exact run_stepStar 64 (shapeWitness n)

/-- The shape change's term is closed: it mentions no free variable. -/
theorem shape_closed (n : Nat) : Closed (shapeWitness n) := by rfl

/-- The shape change's value is a λPure value. -/
theorem shapeValue_value (n : Nat) : Value (shapeValue n) :=
  Value.con2 (quoteSlot_value (.full n)) (quoteSlot_value .empty)

/-- The shape change's two evaluations agree, at an arbitrary payload: the
agreement does not depend on the payload's size. -/
theorem shape_agreement (n : Nat) :
    evalArray (shapeWitness n) = some (shapeValue n) :=
  evalArray_sound (shape_own n) (shape_closed n) (shape_stepStar n) (shapeValue_value n)

/-- The quotation lemma at the shape change. -/
theorem shape_no_root (n : Nat) : hasRoot (shapeValue n) = false :=
  evalArray_no_root (shape_own n) (shape_agreement n)

#guard decide (evalArray (shapeWitness 7) = some (shapeValue 7))
#guard decide (evalArray (shapeWitness (10 ^ 30)) = some (shapeValue (10 ^ 30)))

/-! ## The refusals, and their paired controls

Each refusal is a theorem about a specific expression — an inversion of the rules
of `Own` — and each stands beside an expression of the same purpose that the
rules do admit, with the admitted one's value evaluated. None of them is refused
for being outside A-normal form: each expression's shape is the shape the rule
asks for, and what is refused is the ownership it would need. -/

/-- The aliasing the hand-off refuses: a binding whose bound term is the cell's
own name, which would give the cell a second name. -/
theorem alias_refused :
    ¬ Own Γ₁ .none (.bind 1 (.var 0) (.var 0)) (.obs slotObs) :=
  own_alias_bind_absent (Γ := Γ₁) (x := 0) (y := 1) (e₂ := .var 0) (τ := .obs slotObs)
    (by decide)

/--
error: Application type mismatch: The argument
  Own.obs h
has type
  Own Γ₁ Owner.none (Expr.var 0) (Ty.obs Scidonia.FracPerm.StateVar.Layout5.ObsDesc.nat)
but is expected to have type
  Own Γ₁ Owner.none (Expr.var 0) Ty.cell
in the application
  Own.cellBind 1 (Expr.var 0) (Expr.var 1) (Own.obs h)
-/
#guard_msgs (whitespace := lax) in
example (h : Obs Γ₁ (.var 0) .nat) (hy : Γ₁.extend 1 .cell 1 = none)
    (hobs : Obs (Γ₁.extend 1 .cell) (.var 1) slotObs) :
    Own Γ₁ .none (.bind 1 (.var 0) (.var 1)) (.obs slotObs) :=
  Own.cellBind 1 (.var 0) (.var 1) (Own.obs (κ := .none) h) hy (Own.obs hobs)

/-- The control beside the refusal: the same binding shape whose bound term is a
write through the owner, so the fresh name is the owner of what it binds. This is
the hand-off's own body, admitted at the owner `0`. -/
def transferBody : Expr :=
  .bind 1 (.store (.var 0) 0 (quoteSlot (.full 9)))
    (.matchC (.var 1) rootTag [2] (.con2 pairTag (.var 2) (.var 2)))

/-- The hand-off's body is admitted at the owner `0`. -/
theorem transferBody_own :
    Own Γ₁ (.held 0) transferBody (.obs (.pair slotObs slotObs)) := by
  unfold transferBody
  refine own_transfer_bind (Γ := Γ₁) (x := 0) (y := 1) (a := quoteSlot (.full 9))
    (by decide) (by decide) (Obs.full 9) ?_
  refine Own.read 1 2 _ (by decide) (by decide) ?_
  exact Own.obs (Obs.pair (Obs.var 2 (by decide) Fragment.slot)
    (Obs.var 2 (by decide) Fragment.slot))

/-- The control as a closed program: the root construction binds the cell's
handle, and the transfer runs against it. -/
def transferTerm : Expr := .bind 0 (root (.full 7)) transferBody

/-- The control is admitted at the empty context, so the runner evaluates it. -/
theorem transfer_own :
    Own (TyEnv.empty : TyEnv) .none transferTerm (.obs (.pair slotObs slotObs)) := by
  unfold transferTerm
  exact Own.cellBind 0 (root (.full 7)) transferBody (Own.fresh (Obs.full 7))
    (by decide) transferBody_own

#guard decide
  (evalArray transferTerm = some (.con2 pairTag (quoteSlot (.full 9)) (quoteSlot (.full 9))))

/--
error: Expression
  decide (evalArray transferTerm = some (Expr.con2 pairTag (quoteSlot (Slot.full 7)) (quoteSlot (Slot.full 9))))
did not evaluate to `true`
-/
#guard_msgs (whitespace := lax) in
#guard decide
  (evalArray transferTerm = some (.con2 pairTag (quoteSlot (.full 7)) (quoteSlot (.full 9))))

/-- The self-write the rules refuse: the written value is the cell's own name,
and the value of a write has to be a slot observation. -/
theorem selfWrite_refused :
    ¬ Own Γ₁ (.held 0) (.store (.var 0) 0 (.var 0)) .cell :=
  own_store_self_absent (Γ := Γ₁) (x := 0) (by decide)

/--
error: Tactic `decide` proved that the proposition
  Γ₁ 0 = some (Ty.obs slotObs)
is false
-/
#guard_msgs (whitespace := lax) in
example : Obs Γ₁ (.var 0) slotObs := Obs.var 0 (by decide) Fragment.slot

/-- The control beside the refusal: the same write with a slot observation as its
value. -/
theorem slotWrite_own :
    Own Γ₁ (.held 0) (.store (.var 0) 0 (quoteSlot (.full 9))) .cell :=
  own_slot_store (Γ := Γ₁) (x := 0) (by decide) (Obs.full 9)

/-- The control's copying side: the existing `slotUpdate` carries the quoted root
of `full 7` to the quoted root of `full 9`. -/
theorem slotWrite_slotUpdate :
    slotUpdate (root (.full 7)) 0 (quoteSlot (.full 9)) = some (root (.full 9)) :=
  slotUpdate_root (.full 7) (.full 9)

#guard decide (unquoteSlot (root (.full 9)) = none)
#guard decide (hasRoot (root (.full 9)) = true)

/-- The read that would return the cell's own name: a `.obs`-typed body must be
an observation, and the owner's name is a cell. -/
theorem readEscape_refused :
    ¬ Own Γ₁ (.held 0) (.matchC (.var 0) rootTag [1] (.var 0)) (.obs slotObs) :=
  own_read_escape_absent (Γ := Γ₁) (x := 0) (y := 1) (τ := .obs slotObs) (by decide)

/--
error: Tactic `decide` proved that the proposition
  Γ₁.extend 1 (Ty.obs slotObs) 0 = some (Ty.obs slotObs)
is false
-/
#guard_msgs (whitespace := lax) in
example : Own Γ₁ (.held 0) (.matchC (.var 0) rootTag [1] (.var 0)) (.obs slotObs) :=
  Own.read 0 1 (.var 0) (by decide) (by decide)
    (Own.obs (Obs.var 0 (by decide) Fragment.slot))

/-- The control beside the refusal: the same read with its own bound observation
returned, which is the detached quotation of the cell's slot. -/
theorem readDetached_own :
    Own Γ₁ (.held 0) (.matchC (.var 0) rootTag [1] (.var 1)) (.obs slotObs) :=
  own_read_slot_return (Γ := Γ₁) (x := 0) (y := 1) (e₂ := .var 1) (o := slotObs)
    (by decide) (by decide) (Own.obs (Obs.var 1 (by decide) Fragment.slot))

#guard decide (evalArray (.matchC (.var 0) rootTag [1] (.var 1)) = none)
#guard decide
  (evalArray (.bind 0 (root (.full 7)) (.matchC (.var 0) rootTag [1] (.var 1))) =
    some (quoteSlot (.full 7)))

/-- The cell-headed pair the pair rule refuses: its components are slot
observations, and the owner's name is a cell. -/
theorem pairCell_refused :
    ¬ Own Γ₁ .none (.con2 pairTag (.var 0) (.var 1)) (.obs (.pair slotObs slotObs)) :=
  own_pair_cell_absent (Γ := Γ₁) (x := 0) (b := .var 1) (by decide)

/--
error: Tactic `decide` proved that the proposition
  Γ₁ 0 = some (Ty.obs slotObs)
is false
-/
#guard_msgs (whitespace := lax) in
example : Obs Γ₁ (.var 0) slotObs := Obs.var 0 (by decide) Fragment.slot

/-- The control beside the refusal: the same pair of two detached slot
observations. -/
theorem pairDetached_own :
    Own Γ₄ .none (.con2 pairTag (.var 1) (.var 3)) (.obs (.pair slotObs slotObs)) := by
  refine own_observation_pair (Γ := Γ₄) (a := 1) (b := 3) (by decide) (by decide)

/-- A second root allocation while a cell is held: the root construction's own
owner is `none`. -/
theorem secondRoot_refused :
    ¬ Own Γ₁ (.held 0) (.con1 rootTag (quoteSlot (.full 9))) .cell :=
  own_fresh_held_absent (Γ := Γ₁) (a := quoteSlot (.full 9)) (x := 0)

/--
error: Type mismatch
  Own.fresh (Obs.full 9)
has type
  Own TyEnv.empty Owner.none (Expr.con1 rootTag (Expr.con1 fullTag (Expr.con0 9))) Ty.cell
but is expected to have type
  Own Γ₁ (Owner.held 0) (Expr.con1 rootTag (quoteSlot (Slot.full 9))) Ty.cell
-/
#guard_msgs (whitespace := lax) in
example : Own Γ₁ (.held 0) (.con1 rootTag (quoteSlot (.full 9))) .cell :=
  Own.fresh (Γ := TyEnv.empty) (Obs.full 9)

/-- The control beside the refusal: the read completes and the write through the
owner happens in its continuation, which is the witness's own shape. -/
theorem readThenWrite_own :
    Own (TyEnv.empty : TyEnv) .none witness (.obs (.pair slotObs slotObs)) :=
  witness_own

/-- A write through the observation a read handed over: the read's continuation
must be an observation, and no write is one. -/
theorem writeDuringRead_refused :
    ¬ Own Γ₁ (.held 0)
        (.matchC (.var 0) rootTag [1] (.store (.var 1) 0 (quoteSlot (.full 9)))) (.obs slotObs) := by
  intro h
  cases h with
  | obs hobs => cases hobs
  | read x y body hx hy hbody => exact own_store_obs_absent hbody

/--
error: Type mismatch
  Own.write 1 hc (Obs.full 9)
has type
  Own Γ₂ (Owner.held 1) ((Expr.var 1).store 0 (Expr.con1 fullTag (Expr.con0 9))) Ty.cell
but is expected to have type
  Own Γ₂ (Owner.held 1) ((Expr.var 1).store 0 (quoteSlot (Slot.full 9))) (Ty.obs slotObs)
-/
#guard_msgs (whitespace := lax) in
example (hc : Γ₂ 1 = some .cell) :
    Own Γ₂ (.held 1) (.store (.var 1) 0 (quoteSlot (.full 9))) (.obs slotObs) :=
  Own.write 1 hc (Obs.full 9)

/-- The control beside the refusal: the write through the *owner* after the read
has ended, in a continuation of the read — the witness's own shape, which reads,
then writes through the owner, then reads the new cell. -/
theorem writeAfterRead_own :
    Own (TyEnv.empty : TyEnv) .none witness (.obs (.pair slotObs slotObs)) :=
  witness_own

/-! ## The omissions, by inversion

There is no rule for an abstraction, an application, a `dup` or a `drop`: the
first fragment is first-order and of the source fragment, so a function, its
application and the two resource instructions the lowering writes are not
admitted at any type. -/

/-- An abstraction is admitted at no type. -/
theorem lam_refused (x : Var) (body : Expr) :
    ¬ Own Γ₁ .none (.lam x body) (.obs slotObs) :=
  own_lam_absent x body

/-- An application is admitted at no type. -/
theorem app_refused (f a : Expr) :
    ¬ Own Γ₁ .none (.app f a) (.obs slotObs) :=
  own_app_absent f a

/-- A `dup` instruction is admitted at no type. -/
theorem dup_refused (x : Var) (e : Expr) :
    ¬ Own Γ₁ .none (.dup x e) (.obs slotObs) :=
  own_dup_absent x e

/-- A `drop` instruction is admitted at no type. -/
theorem drop_refused (x : Var) (e : Expr) :
    ¬ Own Γ₁ .none (.drop x e) (.obs slotObs) :=
  own_drop_absent x e

/-- The control beside the omissions: the sequencing a first-order program writes
instead of an application or an abstraction — a value-producing observation bound
to a fresh name and returned — admitted. -/
theorem seq_own : Own Γ₁ .none (.bind 1 (.con0 5) (.var 1)) (.obs .nat) :=
  Own.obsBind 1 (.con0 5) (.var 1) (Obs.nat 5) (by decide)
    (Own.obs (Obs.var 1 (by decide) Fragment.nat))

/-! ## The sealing

The sealed interpreter is private to its module, so a client cannot name it, and
no public function of the sealed executor accepts an array: the public evaluation
takes a term and returns another, and the runner takes a term and an admission
proof. -/

/-- error: Unknown identifier `exec` -/
#guard_msgs in
example (ρ : VEnv) (arr : Array Slot) (e : Expr) : Option (Expr × Array Slot) :=
  exec ρ arr e

/-- info: Scidonia.RC.OwnershipTyped.evalArray (e : Expr) : Option Expr -/
#guard_msgs (whitespace := lax) in
#check Scidonia.RC.OwnershipTyped.evalArray

/-- info: Scidonia.RC.OwnershipTyped.runFresh {o : Scidonia.FracPerm.StateVar.Layout5.ObsDesc} (e : Expr) :
  Own TyEnv.empty Owner.none e (Ty.obs o) → IO Expr -/
#guard_msgs (whitespace := lax) in
#check Scidonia.RC.OwnershipTyped.runFresh

/-- info: Scidonia.RC.OwnershipTyped.runOn (ρ : VEnv) (a : Array Slot) (e : Expr) :
  Option (Expr × Array Slot) -/
#guard_msgs (whitespace := lax) in
#check Scidonia.RC.OwnershipTyped.runOn

/-
The discipline is a `Prop` judgement and carries no run-time data: the evaluation
takes the term alone, and the runner's proof argument is a proposition.
-/
/-- info: Own : TyEnv → Owner → Expr → Ty → Prop -/
#guard_msgs (whitespace := lax) in
#check @Own

/-- info: WellTyped : TyEnv → Expr → Ty → Prop -/
#guard_msgs (whitespace := lax) in
#check @WellTyped

/-- A client can evaluate a submitted program and read the returned observation. -/
example : evalArray witness = some witnessValue := witness_agreement

/-- A client can run a submitted program; the proof argument is erased. -/
example : runFresh witness witness_own = pure witnessValue := witness_io

/-! ## Axioms

Each of these is asserted: the `#guard_msgs` pins the list `#print axioms` emits,
so a proof that acquires another axiom fails the build rather than printing a
longer list. The principles that appear are the ones this development rests on:
`propext` and `Quot.sound`, and nothing else. -/

/-- info: 'Scidonia.RC.OwnershipTyped.evalArray_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.evalArray_sound

/-- info: 'Scidonia.RC.OwnershipTyped.evalArray_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.evalArray_total

/-- info: 'Scidonia.RC.OwnershipTyped.evalArray_no_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.evalArray_no_root

/-- info: 'Scidonia.RC.OwnershipTyped.runFresh_eq_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.runFresh_eq_pure

/-- info: 'Scidonia.RC.OwnershipTyped.stepStar_value_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.stepStar_value_unique

/-- info: 'Scidonia.RC.OwnershipTyped.runOn_simulate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.runOn_simulate

/-- info: 'Scidonia.RC.OwnershipTyped.denote_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.denote_shape

/-- info: 'Scidonia.RC.OwnershipTyped.subst_inst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.subst_inst

/-- info: 'Scidonia.RC.OwnershipTyped.unquoteSlot_quoteSlot' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.unquoteSlot_quoteSlot

/-- info: 'Scidonia.RC.OwnershipTyped.slotUpdate_root' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.slotUpdate_root

/-- info: 'Scidonia.RC.OwnershipTyped.quoteElSlot_encode' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.quoteElSlot_encode

/-- info: 'Scidonia.RC.OwnershipTyped.own_wellTyped' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.own_wellTyped

/-- info: 'Scidonia.RC.OwnershipTyped.own_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.own_pure

/-- info: 'Scidonia.RC.OwnershipTyped.own_cell_owner' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.own_cell_owner

/-- info: 'Scidonia.RC.OwnershipTyped.evalArray_eq_runOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scidonia.RC.OwnershipTyped.evalArray_eq_runOn

/-- info: 'ScidoniaTest.OwnershipTyped.witness_own' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.OwnershipTyped.witness_own

/-- info: 'ScidoniaTest.OwnershipTyped.witness_agreement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.OwnershipTyped.witness_agreement

/-- info: 'ScidoniaTest.OwnershipTyped.witness_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.OwnershipTyped.witness_total

/-- info: 'ScidoniaTest.OwnershipTyped.witness_io' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.OwnershipTyped.witness_io

/-- info: 'ScidoniaTest.OwnershipTyped.transfer_own' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.OwnershipTyped.transfer_own

/-- info: 'ScidoniaTest.OwnershipTyped.shape_agreement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.OwnershipTyped.shape_agreement

/-- info: 'ScidoniaTest.OwnershipTyped.alias_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ScidoniaTest.OwnershipTyped.alias_refused

end ScidoniaTest.OwnershipTyped

