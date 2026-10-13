/-
The types, constructor tags and quotations of the ownership-typed fragment of
λPure.

This module adds a *type index* and a *quotation* to the calculus of
`Scidonia.RC.Syntax`, and nothing else: it defines no second syntax and no
second semantics, it reuses the existing `Expr` and the existing `Slot`, and it
is the only place the constructor tags the fragment reserves are written down.

**The types.** A `Ty` is a protected cell (`cell`) or an observation of a
description (`obs o`). The descriptions written down here are the constructible
fragment of `Scidonia.FracPerm.StateVar.Layout5.ObsDesc`: the unit, the
naturals, the slot observation `sum unit nat` — the description the existing
`Slot` is encoded against — and a pair of two slot observations. `Fragment`
records that fragment, and the rules of `Scidonia.RC.OwnershipTyped.Judgement`
produce no other description, so `cell` is never an observation and an
observation is never a cell.

**The tags.** `rootTag`, `emptyTag`, `fullTag`, `pairTag` and `unitTag` are
distinct constructor tags of the existing `Ctor` (a natural). They are *not*
disjointness assertions about `Expr`: a natural is quoted as `.con0 n`
(`quoteNat`), so a quoted natural may carry the same number as a structural
tag, and it is the type index of the judgements — never a test on a raw
`Expr` — that tells the two apart. What the tags buy is a quotation that an
admitted program's evaluation can produce and a reader can decode.

**The quotations.** `quoteSlot` writes a `Slot` as a λPure value: the empty slot
is the nullary `emptyTag`, and `full n` is the unary `fullTag` applied to the
quotation of the natural `n`. `root s` is the *logical* cell: the unary
`rootTag` whose field is the quotation of the slot the cell holds — unary on
purpose, because the existing `slotUpdate` has a slot on a unary node and none
on a nullary one. `quotePair` writes a pair of slot observations, and `quoteNat`
and `quoteUnit` the two other descriptions. `unquoteSlot` decodes a quotation of
a slot back to the slot, and the round trip `unquoteSlot (quoteSlot s) = some s`
is the law the evaluation of a read and of a write rests on. `quoteElSlot` is
the same quotation read through the existing isomorphism between `Slot` and
`El slotDesc`, and `quoteElSlot_encode` says the two agree.

**What is proved.** The quotation is a λPure *value* and closed
(`quoteSlot_value`, `quoteSlot_closed`, `root_value`, `root_closed`,
`quotePair_value`), it carries no unary root node (`no_root_quoteSlot`,
`no_root_root`), and it is injective (`quoteSlot_injective`). The unary shape
and the slot index are load-bearing, and the two equations that say so are
stated: a nullary node has no slot zero (`slotUpdate_con0`) and a unary node has
no slot one (`slotUpdate_con1_index`). `slotUpdate_root` is the equation the
write's correspondence is read from — the existing functional `slotUpdate`
carries the quoted root of `s` at slot zero to the quoted root of `t` when the
written value is the quotation of `t` — and `storeRoot_root` is the source
calculus's own write redex at that node.
-/
import Scidonia.RC.Pure
import Scidonia.FracPerm.StateVar.Slot
import Scidonia.FracPerm.StateVar.Layout5

namespace Scidonia.RC

namespace OwnershipTyped

open Scidonia.FracPerm.StateVar (Slot El slotDesc encode decode decode_encode)
open Scidonia.FracPerm.StateVar.Layout5 (ObsDesc)

/-! ## The types -/

/-- A type of the fragment: a protected cell, or an observation of a
description of the constructible fragment. A `cell` is never an observation and
an observation is never a cell. -/
inductive Ty where
  /-- The protected cell. -/
  | cell
  /-- An observation of `o`. -/
  | obs (o : ObsDesc)
deriving DecidableEq, Repr

/-- The slot observation: the description the existing `Slot` is encoded
against, `sum unit nat`. -/
abbrev slotObs : ObsDesc := .sum .unit .nat

/-- The constructible fragment of the observation descriptions: the unit, the
naturals, the slot observation and a pair of two slot observations. It has no
constructor for an array, a struct or a reference, so an element of `ObsEl o` at
a description of this fragment is immutable data. -/
inductive Fragment : ObsDesc → Prop where
  /-- The unit description. -/
  | unit : Fragment .unit
  /-- The description of the naturals. -/
  | nat : Fragment .nat
  /-- The slot observation. -/
  | slot : Fragment slotObs
  /-- A pair of two slot observations. -/
  | pair (h₁ : Fragment slotObs) (h₂ : Fragment slotObs) :
      Fragment (.pair slotObs slotObs)

/-- The fragment's pair description is a fragment. -/
theorem Fragment.pair_self : Fragment (.pair slotObs slotObs) :=
  Fragment.pair Fragment.slot Fragment.slot

/-! ## The tags

Five distinct constructor tags. The numbers are arbitrary; what the lemmas
below use is that they are distinct, which `decide` settles at the literals. -/

/-- The tag of the protected root. -/
def rootTag : Ctor := 0

/-- The tag of the empty slot. -/
def emptyTag : Ctor := 1

/-- The tag of a full slot. -/
def fullTag : Ctor := 2

/-- The tag of a pair of slot observations. -/
def pairTag : Ctor := 3

/-- The tag of the unit observation. -/
def unitTag : Ctor := 4

/-- The root tag is not the full tag. -/
theorem rootTag_ne_fullTag : rootTag ≠ fullTag := by decide

/-- The root tag is not the empty tag. -/
theorem rootTag_ne_emptyTag : rootTag ≠ emptyTag := by decide

/-- The root tag is not the pair tag. -/
theorem rootTag_ne_pairTag : rootTag ≠ pairTag := by decide

/-- The root tag is not the unit tag. -/
theorem rootTag_ne_unitTag : rootTag ≠ unitTag := by decide

/-! ## The quotations -/

/-- A natural quoted as a λPure value: the nullary node `n`. A structural tag is
a natural too, so a quoted natural may coincide with one; the type index of the
judgements is what tells them apart. -/
def quoteNat (n : Nat) : Expr := .con0 n

/-- The unit observation quoted. -/
def quoteUnit : Expr := .con0 unitTag

/-- A slot quoted as a λPure value: the empty slot is the nullary `emptyTag`,
and `full n` is the unary `fullTag` applied to the quotation of `n`. -/
def quoteSlot : Slot → Expr
  | .empty => .con0 emptyTag
  | .full n => .con1 fullTag (.con0 n)

/-- The logical cell holding `s`: the unary `rootTag` whose field is the
quotation of `s`. -/
def root (s : Slot) : Expr := .con1 rootTag (quoteSlot s)

/-- A pair of two slot observations quoted. -/
def quotePair (a b : Expr) : Expr := .con2 pairTag a b

/-- Decode a λPure value as the slot it quotes, or `none` when it quotes none.
The `emptyTag` and `fullTag` cases are the only two that decode, and a slot is
not `Inhabited`, so the result is an `Option` and not a default. -/
def unquoteSlot : Expr → Option Slot
  | .con0 c => if c = emptyTag then some .empty else none
  | .con1 c a => if c = fullTag then (match a with | .con0 n => some (.full n) | _ => none)
                 else none
  | _ => none

/-- Decoding a quotation is the slot itself: the round trip the read and the
write rest on. -/
theorem unquoteSlot_quoteSlot (s : Slot) : unquoteSlot (quoteSlot s) = some s := by
  cases s with
  | empty => simp [quoteSlot, unquoteSlot]
  | full n => simp [quoteSlot, unquoteSlot]

/-- Decoding is injective on the slots, because the round trip names the slot
back. -/
theorem quoteSlot_injective {s t : Slot} (h : quoteSlot s = quoteSlot t) : s = t := by
  have h' := congrArg unquoteSlot h
  rw [unquoteSlot_quoteSlot, unquoteSlot_quoteSlot] at h'
  exact Option.some.inj h'

/-- A quoted natural is a λPure value. -/
theorem quoteNat_value (n : Nat) : Value (quoteNat n) := Value.con0 n

/-- The unit observation quoted is a λPure value. -/
theorem quoteUnit_value : Value quoteUnit := Value.con0 unitTag

/-- A quoted slot is a λPure value. -/
theorem quoteSlot_value : ∀ s : Slot, Value (quoteSlot s)
  | .empty => Value.con0 emptyTag
  | .full n => Value.con1 (Value.con0 n)

/-- The logical cell holding `s` is a λPure value. -/
theorem root_value (s : Slot) : Value (root s) := Value.con1 (quoteSlot_value s)

/-- A quoted pair of slot observations is a λPure value. -/
theorem quotePair_value {a b : Expr} (ha : Value a) (hb : Value b) : Value (quotePair a b) :=
  Value.con2 ha hb

/-- A quoted natural is closed. -/
theorem quoteNat_closed (n : Nat) : Closed (quoteNat n) := rfl

/-- The unit observation quoted is closed. -/
theorem quoteUnit_closed : Closed quoteUnit := rfl

/-- A quoted slot is closed: it mentions no variable. -/
theorem quoteSlot_closed (s : Slot) : Closed (quoteSlot s) := by
  cases s with
  | empty => rfl
  | full n => rfl

/-- The logical cell holding `s` is closed. -/
theorem root_closed (s : Slot) : Closed (root s) := quoteSlot_closed s

/-- A quoted pair of closed observations is closed. -/
theorem quotePair_closed {a b : Expr} (ha : Closed a) (hb : Closed b) :
    Closed (quotePair a b) := by
  rw [Closed] at ha hb ⊢
  simp [quotePair, uses, ha, hb]

/-! ## The names a term binds

The binders of a term as a list, in the style of `uses`. A substitution for a
name the term does not bind walks under no binder of that name, which is the
capture freedom the environment extension of the evaluation is read against. -/

/-- The names a term binds: a binder's own name, and — for an arm — its
binders. -/
def binders : Expr → List Var
  | .var _ => []
  | .lam x body => x :: binders body
  | .app f a => binders f ++ binders a
  | .bind x e₁ e₂ => x :: (binders e₁ ++ binders e₂)
  | .matchC s _ ys body => binders s ++ ys ++ binders body
  | .dup _ e => binders e
  | .drop _ e => binders e
  | .con0 _ => []
  | .con1 _ a => binders a
  | .con2 _ a b => binders a ++ binders b
  | .store s _ v => binders s ++ binders v

/-- A name is bound by an abstraction exactly when it is the abstraction's own
name or is bound by its body. -/
theorem mem_binders_lam {x y : Var} {body : Expr} :
    x ∈ binders (.lam y body) ↔ x = y ∨ x ∈ binders body := by
  simp [binders]

/-- A name is bound by a binding exactly when it is the binding's own name or is
bound by one of its two terms. -/
theorem mem_binders_bind {x y : Var} {e₁ e₂ : Expr} :
    x ∈ binders (.bind y e₁ e₂) ↔ x = y ∨ x ∈ binders e₁ ∨ x ∈ binders e₂ := by
  simp [binders, List.mem_append]

/-- A name is bound by a match exactly when it is bound by the subject, is one
of the arm's binders, or is bound by the arm's body. -/
theorem mem_binders_matchC {x : Var} {s body : Expr} {c : Ctor} {ys : List Var} :
    x ∈ binders (.matchC s c ys body) ↔ x ∈ binders s ∨ x ∈ ys ∨ x ∈ binders body := by
  simp [binders, List.mem_append]

/-! ## The no-root detector

The protected cell's quotation is the only shape an admitted program may *not*
return; a returned observation is built from the observation constructors alone.
`hasRoot` is the syntactic detector of a unary root node, and the quotation
lemma of `Scidonia.RC.OwnershipTyped.Refinement` reads it. -/

/-- Whether a term contains a unary root node. -/
def hasRoot : Expr → Bool
  | .var _ => false
  | .lam _ body => hasRoot body
  | .app f a => hasRoot f || hasRoot a
  | .bind _ e₁ e₂ => hasRoot e₁ || hasRoot e₂
  | .matchC s _ _ body => hasRoot s || hasRoot body
  | .dup _ e => hasRoot e
  | .drop _ e => hasRoot e
  | .con0 _ => false
  | .con1 c a => if c = rootTag then true else hasRoot a
  | .con2 _ a b => hasRoot a || hasRoot b
  | .store s _ v => hasRoot s || hasRoot v

/-- A quoted natural carries no root node. -/
theorem no_root_quoteNat (n : Nat) : hasRoot (quoteNat n) = false := rfl

/-- The unit observation quoted carries no root node. -/
theorem no_root_quoteUnit : hasRoot quoteUnit = false := rfl

/-- A quoted slot carries no root node: its tag is the empty tag or the full
tag, and neither is the root tag. -/
theorem no_root_quoteSlot (s : Slot) : hasRoot (quoteSlot s) = false := by
  cases s with
  | empty => rfl
  | full n => simp [quoteSlot, hasRoot, fullTag, rootTag]

/-- A quoted pair of no-root observations carries no root node. -/
theorem no_root_quotePair {a b : Expr} (ha : hasRoot a = false) (hb : hasRoot b = false) :
    hasRoot (quotePair a b) = false := by
  simp [quotePair, hasRoot, ha, hb]

/-- The logical cell carries a root node: it *is* one. -/
theorem root_hasRoot (s : Slot) : hasRoot (root s) = true := by
  simp [root, hasRoot, rootTag]

/-! ## The existing slot isomorphism

`quoteSlot` is the existing `Slot.encode`/`decode` isomorphism read as λPure
syntax: `quoteElSlot` writes an element of `El slotDesc` as a λPure value, and
`quoteElSlot_encode` says quoting an encoded slot is quoting the slot. Both
inverse laws of the isomorphism are the existing `Slot.decode_encode` and
`Slot.encode_decode`, imported here and not restated. -/

/-- An element of `El slotDesc` quoted as a λPure value: the left summand's unit
is the empty tag, the right summand's natural is the full tag applied to it. -/
def quoteElSlot : El slotDesc → Expr
  | Sum.inl _ => .con0 emptyTag
  | Sum.inr n => .con1 fullTag (.con0 n)

/-- Quoting an encoded slot is quoting the slot: the two writings of the
fragment's slot quotation agree. -/
theorem quoteElSlot_encode (s : Slot) : quoteElSlot (encode s) = quoteSlot s := by
  cases s with
  | empty => rfl
  | full n => rfl

/-- Decoding an element of the slot description and quoting it is quoting the
element: the quotation commutes with the existing isomorphism in the other
direction as well, so the two writings of the fragment's slot quotation agree at
every element of the description and not only at the encoded slots. -/
theorem quoteElSlot_decode (r : El slotDesc) : quoteSlot (decode r) = quoteElSlot r := by
  obtain (u | n) := r
  · cases u
    rfl
  · rfl

/-- Decoding the quotation of a slot's *encoding* is the slot: the round trip
through the existing isomorphism and the fragment's quotation. -/
theorem unquoteSlot_quoteElSlot_encode (s : Slot) :
    unquoteSlot (quoteElSlot (encode s)) = some s := by
  rw [quoteElSlot_encode s]
  exact unquoteSlot_quoteSlot s

/-- Quoting a slot's encoding is quoting the decoded encoding, read through the
existing inverse law `Slot.decode_encode`: the quotation and the isomorphism
agree at the encoded slots. -/
theorem quoteElSlot_encode_decode_encode (s : Slot) :
    quoteElSlot (encode s) = quoteSlot (decode (encode s)) := by
  rw [decode_encode s, quoteElSlot_encode s]

/-! ## The write at the quoted root

The three equations the write's correspondence is read from. The root is unary
and the index is zero: `slotUpdate` is a slot write and not a recursion, so a
nullary node has no slot zero and a unary node has no slot one. -/

/-- The existing functional `slotUpdate` at slot zero of the quoted root: given
the quotation of `t` it yields exactly the quoted root of `t`. Both the node's
field and the written value are `quoteSlot` of a slot, and that is what the
correspondence needs. -/
theorem slotUpdate_root (s t : Slot) :
    slotUpdate (root s) 0 (quoteSlot t) = some (root t) := by
  simp [root, slotUpdate]

/-- The unary shape is load-bearing: a nullary node has no slot zero. -/
theorem slotUpdate_con0 (c : Ctor) (v : Expr) : slotUpdate (.con0 c) 0 v = none := rfl

/-- Slot zero is the unary node's only slot: an index past it is a stuck write,
because `slotUpdate` is not a recursion into a node's fields. -/
theorem slotUpdate_con1_index (c : Ctor) (a v : Expr) : slotUpdate (.con1 c a) 1 v = none :=
  rfl

/-- The source calculus's write redex at the quoted root: the term the array
evaluation of a write has to agree with. -/
theorem storeRoot_root (s t : Slot) :
    Root (.store (root s) 0 (quoteSlot t)) (root t) :=
  Root.storeVal (root_value s) (quoteSlot_value t) (slotUpdate_root s t)

end OwnershipTyped

end Scidonia.RC
