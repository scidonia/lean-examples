/-
The layout-indexed quotation of a tree state, and the observation encoding it
agrees with.

**What this adds.** `Scidonia.FracPerm.StateVar.Layout5` has a state `State d`
for a layout `d` — a leaf of the observation universe, a binary struct, or an
array — and a *path* into it. This module writes a state as a term of the
existing λPure syntax (`Scidonia.RC.Syntax.Expr`), so that the copying reduction
and a direct interpreter can be compared at one value: *the quotation*. It
defines no second syntax, no second state type and no second path grammar.

**The leaf encoding.** `quoteEl` writes an element of the observation universe
`ObsEl o` as a λPure value. The slot description is the one case that reuses an
existing encoding rather than inventing one: `quoteEl` at `sum unit nat` writes
the element exactly as `Scidonia.RC.OwnershipTyped.quoteElSlot` writes it, so the
slot quotation of the one-cell fragment and the leaf quotation of this module are
the same term (`quoteEl_slotDesc`, `quoteEl_quoteSlot`). Its inverse `unquoteEl`
decodes, and `unquoteEl_quoteEl` is the round trip the read and the write rest
on.

**The node encoding.** `cellVal` writes a state as the *protected node's* value:
a leaf is the unary `rootTag` node whose field is the leaf's observation — this is
exactly `Scidonia.RC.OwnershipTyped.root` at the slot description
(`cellVal_leaf_slot`) — a struct is the binary `structTag` node whose fields are
its components' node values, and an array is the `consTag`/`nilTag` spine of its
elements' node values, in order. Every node value is a λPure value and closed
(`cellVal_value`, `cellVal_closed`), and a *leaf* carries the unary root node
while a struct or array node does not: that is what lets a read at a leaf and a
descent into a struct be told apart by the node's own tag.

**What is proved.** Decoding inverts the quotation (`unquoteVal_cellVal`) and
hence the quotation is injective (`cellVal_injective`); a *leaf's* observation
carries no protected node, subtree or array (`quoteEl_hasProtected`), where
`hasProtected` is the syntactic detector of a unary root node or a binary struct
or array node; `leafObsPath?` resolves a path to an observation path exactly when
its end is a leaf; `nav` navigates a quotation along a path and `nav_cellVal` is
the path-resolution law — navigating the quotation of a state along an in-bounds
path is the quotation of the state's own node there; and `decodeValue` inverts
the state variable library's own `encodeObs`, so a read's `Value` and this
module's quotation describe one observation.
-/
import Scidonia.RC.OwnershipTyped.Model
import Scidonia.FracPerm.StateVar.Sealed

namespace Scidonia.RC

namespace TreeOwnership

open Scidonia.FracPerm.StateVar (Slot El slotDesc encode)
open Scidonia.FracPerm.StateVar.Layout5
open Scidonia.RC.OwnershipTyped

/-! ## The tags

The constructor tags the tree fragment reserves, distinct from the tags of the
one-cell fragment. They are not disjointness assertions about `Expr`: a natural
is quoted as `.con0 n` and may coincide numerically with a tag, which is why the
detector below is read for the unary and binary node forms, and why a rule that
admits a term reads the term's layout alongside its shape.
-/

/-- The tag of a struct node: a binary node whose fields are its components'
nodes. -/
def structTag : Ctor := 5

/-- The tag of the empty array spine. -/
def nilTag : Ctor := 6

/-- The tag of a nonempty array spine: a binary node whose first field is an
element's node and whose second field is the rest of the spine. -/
def consTag : Ctor := 7

/-- The tag of a left summand. -/
def inlTag : Ctor := 8

/-- The tag of a right summand. -/
def inrTag : Ctor := 9

/-- The tag of an optional's `some`. -/
def someTag : Ctor := 10

/-- The tag of an optional's `none`. -/
def noneTag : Ctor := 11

/-- The tag of a false boolean. -/
def falseTag : Ctor := 12

/-- The tag of a true boolean. -/
def trueTag : Ctor := 13

/-- The tag of a machine word. -/
def uintTag : Ctor := 14

/-- The struct tag is not the pair tag: a struct node and a pair of two
observations are different shapes of binary node. -/
theorem structTag_ne_pairTag : structTag ≠ pairTag := by decide

/-- The cons tag is not the struct tag: a spine and a struct are different
shapes of binary node. -/
theorem consTag_ne_structTag : consTag ≠ structTag := by decide

/-- The cons tag is not the pair tag. -/
theorem consTag_ne_pairTag : consTag ≠ pairTag := by decide

/-! ## The leaf encoding -/

/-- An element of the observation universe quoted as a λPure value. A unit is the
nullary unit tag, a natural the nullary node `n`, a machine word the unary word
tag applied to the word's natural, a boolean a nullary boolean tag, a sum the
unary inl/inr tag applied to the summand, an optional the nullary none tag or the
unary some tag, and a pair the binary pair tag of the two components. The slot
description — the left unit or the right natural of `sum unit nat` — is written
exactly as the one-cell fragment's `quoteElSlot` writes it. -/
def quoteEl : (o : ObsDesc) → ObsEl o → Expr
  | .unit, _ => .con0 unitTag
  | .nat, n => .con0 n
  | .uint, n => .con1 uintTag (.con0 n.toNat)
  | .bool, b => .con0 (if b then trueTag else falseTag)
  | .sum .unit .nat, Sum.inl _ => .con0 emptyTag
  | .sum .unit .nat, Sum.inr n => .con1 fullTag (.con0 n)
  | .sum a _, Sum.inl x => .con1 inlTag (quoteEl a x)
  | .sum _ b, Sum.inr y => .con1 inrTag (quoteEl b y)
  | .option _, none => .con0 noneTag
  | .option a, some x => .con1 someTag (quoteEl a x)
  | .pair a b, (x, y) => .con2 pairTag (quoteEl a x) (quoteEl b y)

/-- Decode a λPure value as the element of `o` it quotes, or `none` when it
quotes none of that description. The slot description decodes as the one-cell
fragment's `quoteSlot` encodes it. -/
def unquoteEl : (o : ObsDesc) → Expr → Option (ObsEl o)
  | .unit, .con0 c => if c = unitTag then some () else none
  | .nat, .con0 n => some n
  | .uint, .con1 c a =>
      if c = uintTag then (match a with | .con0 n => some (UInt64.ofNat n) | _ => none) else none
  | .bool, .con0 c =>
      if c = trueTag then some true else if c = falseTag then some false else none
  | .sum .unit .nat, .con0 c => if c = emptyTag then some (Sum.inl ()) else none
  | .sum .unit .nat, .con1 c a =>
      if c = fullTag then (match a with | .con0 n => some (Sum.inr n) | _ => none) else none
  | .sum a b, .con1 c x =>
      if c = inlTag then (unquoteEl a x).map Sum.inl
      else if c = inrTag then (unquoteEl b x).map Sum.inr else none
  | .option _, .con0 c => if c = noneTag then some none else none
  | .option a, .con1 c x => if c = someTag then (unquoteEl a x).map some else none
  | .pair a b, .con2 c x y =>
      if c = pairTag then
        (unquoteEl a x).bind (fun u => (unquoteEl b y).map (fun v => (u, v)))
      else none
  | _, _ => none

/-- The boolean case of the round trip in the form the case analysis of a sum
leaves it. -/
theorem unquoteEl_bool_round (b : Bool) : (if b = true then some true else some false) = some b := by
  cases b <;> rfl

/-- The slot description's quotation is the one-cell fragment's element
quotation: a cell's slot and a leaf's element quote the same term. -/
theorem quoteEl_slotDesc (x : El slotDesc) : quoteEl (.sum .unit .nat) x = quoteElSlot x := by
  obtain (u | n) := x
  · cases u; rfl
  · rfl

/-- The slot description's quotation of a slot is the one-cell fragment's slot
quotation. -/
theorem quoteEl_quoteSlot (s : Slot) : quoteEl (.sum .unit .nat) (encode s) = quoteSlot s := by
  cases s <;> rfl

/-- Decoding the one-cell fragment's slot quotation is the encoded slot. -/
theorem unquoteEl_quoteSlot (s : Slot) :
    unquoteEl (.sum .unit .nat) (quoteSlot s) = some (encode s) := by
  cases s <;> rfl

/-- Decoding a quotation is the element it quotes: the round trip the read and the
write rest on, at every description. -/
theorem unquoteEl_quoteEl : ∀ (o : ObsDesc) (x : ObsEl o), unquoteEl o (quoteEl o x) = some x
  | .unit, x => by cases x; rfl
  | .nat, n => rfl
  | .uint, n => by simp [quoteEl, unquoteEl, UInt64.ofNat_toNat]
  | .bool, b => by cases b <;> rfl
  | .sum .unit .nat, x => by cases x <;> rfl
  | .sum a b, x => by
      revert x
      cases a <;> cases b <;> intro x <;> cases x <;>
        simp_all [quoteEl, unquoteEl, unquoteEl_quoteEl, unquoteEl_bool_round,
          UInt64.ofNat_toNat, unitTag, emptyTag, fullTag, inlTag, inrTag,
          trueTag, falseTag, uintTag]
  | .option a, x => by
      cases x with
      | none => rfl
      | some y => simp [quoteEl, unquoteEl, unquoteEl_quoteEl a y]
  | .pair a b, x => by
      obtain ⟨u, v⟩ := x
      simp [quoteEl, unquoteEl, unquoteEl_quoteEl a u, unquoteEl_quoteEl b v]

/-- Decoding is injective on the elements of one description, because the round
trip names the element back. -/
theorem quoteEl_injective {o : ObsDesc} {x y : ObsEl o} (h : quoteEl o x = quoteEl o y) :
    x = y := by
  have h' := congrArg (unquoteEl o) h
  rw [unquoteEl_quoteEl, unquoteEl_quoteEl] at h'
  exact Option.some.inj h'

/-- A quoted observation is a λPure value: every case is a node whose fields are
values. -/
theorem quoteEl_value : ∀ (o : ObsDesc) (x : ObsEl o), Value (quoteEl o x)
  | .unit, _ => Value.con0 unitTag
  | .nat, n => Value.con0 n
  | .uint, n => Value.con1 (Value.con0 n.toNat)
  | .bool, b => Value.con0 _
  | .sum .unit .nat, Sum.inl _ => Value.con0 emptyTag
  | .sum .unit .nat, Sum.inr n => Value.con1 (Value.con0 n)
  | .sum a b, x => by
      revert x
      cases a <;> cases b <;> intro x <;> cases x <;>
        first
          | exact Value.con0 _
          | exact Value.con1 (Value.con0 _)
          | exact Value.con1 (quoteEl_value _ _)
  | .option _, none => Value.con0 noneTag
  | .option a, some x => Value.con1 (quoteEl_value a x)
  | .pair a b, (x, y) => Value.con2 (quoteEl_value a x) (quoteEl_value b y)

/-- A quoted observation is closed: it mentions no variable. -/
theorem quoteEl_closed (o : ObsDesc) : ∀ x : ObsEl o, Closed (quoteEl o x) := by
  induction o with
  | unit => intro x; cases x; rfl
  | nat => intro n; rfl
  | uint => intro n; rfl
  | bool => intro b; rfl
  | sum a b iha ihb =>
      simp only [Closed] at iha ihb
      intro x
      cases a <;> cases b <;> cases x <;>
        first
          | rfl
          | (rw [Closed]; simp only [quoteEl, uses]
             first | exact iha _ | exact ihb _ | rfl)
  | option a iha =>
      simp only [Closed] at iha
      intro x
      cases x <;>
        first
          | rfl
          | (rw [Closed]; simp only [quoteEl, uses]; exact iha _)
  | pair a b iha ihb =>
      simp only [Closed] at iha ihb
      intro x
      obtain ⟨u, v⟩ := x
      rw [Closed]
      simp [quoteEl, uses, iha, ihb]

/-! ## The state variable library's encoding

The library's own observation encoding is `encodeObs`, whose result is its
`Value`. A read returns one, and the direct interpreter needs the element it
encodes — not the encoding alone, which is lossy about which description it came
from. `decodeValue` is that inverse. -/

/-- Decode the state variable library's `Value` back to the element of `o` it
encodes, or `none` when it encodes none of that description. -/
def decodeValue : (o : ObsDesc) → Scidonia.FracPerm.StateVar.Value → Option (ObsEl o)
  | .unit, .unit => some ()
  | .nat, .nat n => some n
  | .uint, .uint n => some n
  | .bool, .bool b => some b
  | .sum a _, .inl x => (decodeValue a x).map Sum.inl
  | .sum _ b, .inr y => (decodeValue b y).map Sum.inr
  | .option _, .none => some none
  | .option a, .some x => (decodeValue a x).map some
  | .pair a b, .pair x y =>
      (decodeValue a x).bind (fun u => (decodeValue b y).map (fun v => (u, v)))
  | _, _ => none

/-- Decoding the library's encoding of an element is the element: the read's
`Value` and this module's quotation describe one observation. -/
theorem decodeValue_encodeObs : ∀ (o : ObsDesc) (x : ObsEl o),
    decodeValue o (encodeObs o x) = some x
  | .unit, x => by cases x; rfl
  | .nat, n => rfl
  | .uint, n => rfl
  | .bool, b => rfl
  | .sum a b, x => by
      cases x with
      | inl u => simp [encodeObs, decodeValue, decodeValue_encodeObs a u]
      | inr v => simp [encodeObs, decodeValue, decodeValue_encodeObs b v]
  | .option a, x => by
      cases x with
      | none => rfl
      | some y => simp [encodeObs, decodeValue, decodeValue_encodeObs a y]
  | .pair a b, x => by
      obtain ⟨u, v⟩ := x
      simp [encodeObs, decodeValue, decodeValue_encodeObs a u, decodeValue_encodeObs b v]

/-- The decoding of a read's `Value` is the element it encodes. -/
theorem decodeValue_of_eq {o : ObsDesc} {x : ObsEl o} {v : Scidonia.FracPerm.StateVar.Value}
    (h : v = encodeObs o x) : decodeValue o v = some x := by
  subst h
  exact decodeValue_encodeObs o x

/-! ## The node encoding -/

mutual

/-- The value of the protected node at a layout's root: a leaf as the unary
`rootTag` node whose field is the leaf's observation, a struct as the binary
`structTag` node of its components' node values, and an array as the
`consTag`/`nilTag` spine of its elements' node values. -/
def cellVal : (d : Layout) → State d → Expr
  | .leaf o, x => .con1 rootTag (quoteEl o x)
  | .struct a b, (u, v) => .con2 structTag (cellVal a u) (cellVal b v)
  | .arr a, s => spineVal a s.toList

/-- The `nil`/`cons` spine of an array's element node values, in order. -/
def spineVal : (a : Layout) → List (State a) → Expr
  | _, [] => .con0 nilTag
  | a, x :: t => .con2 consTag (cellVal a x) (spineVal a t)

end

/-- A leaf's node value is the unary root node of its observation. -/
theorem cellVal_leaf (o : ObsDesc) (x : ObsEl o) :
    cellVal (.leaf o) x = .con1 rootTag (quoteEl o x) := by
  simp [cellVal]

/-- The empty spine is the nullary nil node. -/
theorem spineVal_nil (a : Layout) : spineVal a [] = .con0 nilTag := by
  simp [spineVal]

/-- A nonempty spine is the binary cons node of its head and its tail. -/
theorem spineVal_cons (a : Layout) (x : State a) (t : List (State a)) :
    spineVal a (x :: t) = .con2 consTag (cellVal a x) (spineVal a t) := by
  simp [spineVal]

/-- A leaf's node value at the slot description is the one-cell fragment's root:
the two quotations agree at the description the fragment's cell is encoded
against. -/
theorem cellVal_leaf_slot (s : Slot) :
    cellVal (.leaf (.sum .unit .nat)) (Scidonia.FracPerm.StateVar.encode s) = root s := by
  cases s <;>
    simp [cellVal, quoteEl, root, quoteSlot, Scidonia.FracPerm.StateVar.encode,
      emptyTag, fullTag]

/-- A struct's node value is the binary struct node of its components'. -/
theorem cellVal_struct (a b : Layout) (u : State a) (v : State b) :
    cellVal (.struct a b) (u, v) = .con2 structTag (cellVal a u) (cellVal b v) := by
  simp [cellVal]

/-- An array's node value is its spine. -/
theorem cellVal_arr (a : Layout) (s : Array (State a)) :
    cellVal (.arr a) s = spineVal a s.toList := by
  simp [cellVal]

mutual

/-- A node value is a λPure value. -/
theorem cellVal_value : ∀ (d : Layout) (s : State d), Value (cellVal d s)
  | .leaf o, x => by rw [cellVal_leaf]; exact Value.con1 (quoteEl_value o x)
  | .struct a b, (u, v) => by
      rw [cellVal_struct]; exact Value.con2 (cellVal_value a u) (cellVal_value b v)
  | .arr a, s => by rw [cellVal_arr]; exact spineVal_value a s.toList

/-- Every spine's value is a λPure value. -/
theorem spineVal_value : ∀ (a : Layout) (l : List (State a)), Value (spineVal a l)
  | a, [] => by rw [spineVal_nil]; exact Value.con0 nilTag
  | a, x :: t => by
      rw [spineVal_cons]; exact Value.con2 (cellVal_value a x) (spineVal_value a t)

end

mutual

/-- A node value is closed: it mentions no variable. -/
theorem cellVal_closed : ∀ (d : Layout) (s : State d), Closed (cellVal d s)
  | .leaf o, x => by
      rw [cellVal_leaf, Closed]
      exact quoteEl_closed o x
  | .struct a b, (u, v) => by
      have h₁ := cellVal_closed a u
      have h₂ := cellVal_closed b v
      rw [Closed] at h₁ h₂
      rw [cellVal_struct, Closed]
      simp [uses, h₁, h₂]
  | .arr a, s => by rw [cellVal_arr]; exact spineVal_closed a s.toList

/-- Every spine's value is closed. -/
theorem spineVal_closed : ∀ (a : Layout) (l : List (State a)), Closed (spineVal a l)
  | a, [] => by rw [spineVal_nil]; exact rfl
  | a, x :: t => by
      have h₁ := cellVal_closed a x
      have h₂ := spineVal_closed a t
      rw [Closed] at h₁ h₂
      rw [spineVal_cons, Closed]
      simp [uses, h₁, h₂]

end

/-! ## The sub-state accessor and the partial node accessor -/

/-- The state at the end of a path, or the layout's default state when an index
along the path is out of bounds: the accessor a node value is read at. An
out-of-bounds index addresses nothing, and the default state is what an array slot
holds when nothing was taken out of it. -/
def subAt {d : Layout} : (p : Path d) → State d → State (At p)
  | .here, s => s
  | .left q, s => subAt q s.1
  | .right q, s => subAt q s.2
  | .index i q, s =>
      match s[i]? with
      | some e => subAt q e
      | none => stateDefault (At q)

/-- The node value at a path: the state's own node there, quoted. -/
def nodeVal {d : Layout} (p : Path d) (s : State d) : Expr := cellVal (At p) (subAt p s)

/-- Whether every index along a path addresses an element of the state: the
condition under which the node accessor and the navigation agree. -/
def InBounds : {d : Layout} → (p : Path d) → State d → Prop
  | _, .here, _ => True
  | _, .left q, s => InBounds q s.1
  | _, .right q, s => InBounds q s.2
  | _, .index i q, s => ∃ e, s[i]? = some e ∧ InBounds q e

/-- The sub-state at the root path is the state. -/
@[simp] theorem subAt_here {d : Layout} (s : State d) : subAt (Path.here : Path d) s = s := rfl

/-- The sub-state at a struct's left component. -/
theorem subAt_left {a b : Layout} (q : Path a) (s : State (.struct a b)) :
    subAt (.left q) s = subAt q s.1 := rfl

/-- The sub-state at a struct's right component. -/
theorem subAt_right {a b : Layout} (q : Path b) (s : State (.struct a b)) :
    subAt (.right q) s = subAt q s.2 := rfl

/-- The sub-state at an array element: the element at the index, or the layout's
default when the index is out of bounds. -/
theorem subAt_index {a : Layout} (i : Nat) (q : Path a) (s : Array (State a)) :
    subAt (.index i q) s =
      (match s[i]? with | some e => subAt q e | none => stateDefault (At q)) := rfl

/-- The node value at the root path is the root's. -/
@[simp] theorem nodeVal_here {d : Layout} (s : State d) :
    nodeVal (Path.here : Path d) s = cellVal d s := rfl

/-- The node value at a path is a λPure value. -/
theorem nodeVal_value {d : Layout} (p : Path d) (s : State d) : Value (nodeVal p s) :=
  cellVal_value (At p) (subAt p s)

/-- The node value at a path is closed. -/
theorem nodeVal_closed {d : Layout} (p : Path d) (s : State d) : Closed (nodeVal p s) :=
  cellVal_closed (At p) (subAt p s)

/-! ## The decoder -/

/-- The field of a unary root node, or `none` when the value is not one: the
wrapper a leaf's node value carries is stripped before its observation is
decoded. -/
def unwrapRoot : Expr → Option Expr
  | .con1 c w => if c = rootTag then some w else none
  | _ => none

mutual

/-- Decode a *node* value as the state it quotes, or `none`: a leaf's root node
is unwrapped and its field decoded, a struct node's two fields are decoded, and
a spine is decoded and turned into an array. -/
def unquoteVal : (d : Layout) → Expr → Option (State d)
  | .leaf o, v => (unwrapRoot v).bind (unquoteEl o)
  | .struct a b, v =>
      match v with
      | .con2 c x y =>
          if c = structTag then
            (unquoteVal a x).bind (fun u => (unquoteVal b y).map (fun w => (u, w)))
          else none
      | _ => none
  | .arr a, v => (unquoteSpine a v).map (fun l => l.toArray)

/-- Decode a λPure value as the list of element node values a `nil`/`cons` spine
quotes, or `none`. -/
def unquoteSpine : (a : Layout) → Expr → Option (List (State a))
  | _, .con0 c => if c = nilTag then some [] else none
  | a, .con2 c x t =>
      if c = consTag then
        (unquoteVal a x).bind (fun u => (unquoteSpine a t).map (fun l => u :: l))
      else none
  | _, _ => none

end

/-- A spine's decoder inverts its quotation, given the element decoder's own
round trip: the list recursion the array case of the state round trip rests on. -/
theorem unquoteSpine_spineVal_of (a : Layout)
    (h : ∀ x : State a, unquoteVal a (cellVal a x) = some x) :
    ∀ (l : List (State a)), unquoteSpine a (spineVal a l) = some l
  | [] => by simp [spineVal, unquoteSpine]
  | x :: t => by
      simp [spineVal, unquoteSpine, h x, unquoteSpine_spineVal_of a h t]

/-- A state's node decoder inverts its node value. -/
theorem unquoteVal_cellVal (d : Layout) : ∀ s : State d, unquoteVal d (cellVal d s) = some s := by
  induction d with
  | leaf o =>
      intro x
      simp [cellVal, unquoteVal, unwrapRoot, unquoteEl_quoteEl]
  | struct a b iha ihb =>
      intro s
      obtain ⟨u, v⟩ := s
      simp [cellVal, unquoteVal, iha u, ihb v]
  | arr a iha =>
      intro s
      simp only [cellVal, unquoteVal]
      rw [unquoteSpine_spineVal_of a iha s.toList]
      simp [Array.toArray_toList]

/-- A spine's decoder inverts its quotation. -/
theorem unquoteSpine_spineVal (a : Layout) (l : List (State a)) :
    unquoteSpine a (spineVal a l) = some l :=
  unquoteSpine_spineVal_of a (unquoteVal_cellVal a) l

/-- Decoding is injective on the states of one layout. -/
theorem cellVal_injective {d : Layout} {s t : State d} (h : cellVal d s = cellVal d t) :
    s = t := by
  have h' := congrArg (unquoteVal d) h
  rw [unquoteVal_cellVal d, unquoteVal_cellVal d] at h'
  exact Option.some.inj h'

/-! ## The detector -/

/-- Whether a term contains a unary root node or a binary struct or array node:
the syntactic detector of a protected node, subtree or array. A natural's
quotation is a nullary node and may coincide numerically with a tag, which is why
the nullary form is not tested; the shapes this detector is read for are the
unary and binary nodes. -/
def hasProtected : Expr → Bool
  | .var _ => false
  | .lam _ b => hasProtected b
  | .app f a => hasProtected f || hasProtected a
  | .bind _ e₁ e₂ => hasProtected e₁ || hasProtected e₂
  | .matchC s _ _ b => hasProtected s || hasProtected b
  | .dup _ e => hasProtected e
  | .drop _ e => hasProtected e
  | .con0 _ => false
  | .con1 c a => c = rootTag || hasProtected a
  | .con2 c a b => c = structTag || c = consTag || hasProtected a || hasProtected b
  | .store s _ v => hasProtected s || hasProtected v

/-- A nullary node carries no protected node. -/
theorem hasProtected_con0 (c : Ctor) : hasProtected (.con0 c) = false := rfl

/-- A unary node whose tag is not the root tag carries no protected node exactly
when its field does not. -/
theorem hasProtected_con1_ne {c : Ctor} {a : Expr} (hc : c ≠ rootTag)
    (h : hasProtected a = false) : hasProtected (.con1 c a) = false := by
  simp [hasProtected, hc, h]

/-- A binary node whose tag is neither the struct tag nor the cons tag carries no
protected node exactly when its fields do not. -/
theorem hasProtected_con2_ne {c : Ctor} {a b : Expr} (hc : c ≠ structTag)
    (hc' : c ≠ consTag) (ha : hasProtected a = false) (hb : hasProtected b = false) :
    hasProtected (.con2 c a b) = false := by
  simp [hasProtected, hc, hc', ha, hb]

/-- A leaf's observation carries no protected node, subtree or array: every
observation a read returns is detached. -/
theorem quoteEl_hasProtected (o : ObsDesc) : ∀ x : ObsEl o, hasProtected (quoteEl o x) = false := by
  induction o with
  | unit => intro x; cases x; rfl
  | nat => intro n; rfl
  | uint => intro n; exact hasProtected_con1_ne (by decide) rfl
  | bool => intro b; rfl
  | sum a b iha ihb =>
      intro x
      cases a <;> cases b <;> cases x <;>
        first
          | rfl
          | exact hasProtected_con1_ne (by decide) rfl
          | exact hasProtected_con1_ne (by decide) (iha _)
          | exact hasProtected_con1_ne (by decide) (ihb _)
  | option a iha =>
      intro x
      cases x <;>
        first
          | rfl
          | exact hasProtected_con1_ne (by decide) (iha _)
  | pair a b iha ihb =>
      intro x
      obtain ⟨u, v⟩ := x
      exact hasProtected_con2_ne (by decide) (by decide) (iha u) (ihb v)

/-- A leaf node's value carries the protected root node: it is one. -/
theorem cellVal_leaf_hasProtected (o : ObsDesc) (x : ObsEl o) :
    hasProtected (cellVal (.leaf o) x) = true := by
  simp [cellVal, hasProtected, rootTag]

/-! ## The binding path of a read -/

/-- The observation path a path *is*, when it ends at a leaf: the description at
its end and the proof. A path whose end is a struct or an array has none, and a
read at a handle whose path has one is a read of a leaf's observation. The
function is a structural recursion on the path, so every layout case is decided
by the path's own index. -/
def leafObsPath? {d : Layout} : (p : Path d) → Option (ObsPath d)
  | .here =>
      match d with
      | .leaf o => some ⟨.here, o, rfl⟩
      | .struct _ _ => none
      | .arr _ => none
  | .left q =>
      match leafObsPath? q with
      | some r => some ⟨.left r.path, r.obs, r.leaf⟩
      | none => none
  | .right q =>
      match leafObsPath? q with
      | some r => some ⟨.right r.path, r.obs, r.leaf⟩
      | none => none
  | .index i q =>
      match leafObsPath? q with
      | some r => some ⟨.index i r.path, r.obs, r.leaf⟩
      | none => none

/-- The path a resolved observation path came from is that path. -/
theorem leafObsPath?_some : ∀ {d : Layout} (p : Path d) {q : ObsPath d},
    leafObsPath? p = some q → q.path = p := by
  intro d p
  induction p with
  | here =>
      intro q h
      simp only [leafObsPath?] at h
      split at h
      · cases h; rfl
      · simp at h
      · simp at h
  | left p ih =>
      intro q h
      simp only [leafObsPath?] at h
      split at h
      · rename_i r hr
        cases h
        exact congrArg Path.left (ih hr)
      · simp at h
  | right p ih =>
      intro q h
      simp only [leafObsPath?] at h
      split at h
      · rename_i r hr
        cases h
        exact congrArg Path.right (ih hr)
      · simp at h
  | index i p ih =>
      intro q h
      simp only [leafObsPath?] at h
      split at h
      · rename_i r hr
        cases h
        exact congrArg (Path.index i) (ih hr)
      · simp at h

/-! ## Path navigation and the path-resolution law -/

/-- The unwrapped node of a value: the unary root node's field, or the value
itself when it is not one. -/
def unwrapNode : Expr → Expr
  | .con1 c w => if c = rootTag then w else .con1 c w
  | v => v

/-- Navigate a `nil`/`cons` spine to its `i`-th element's node. -/
def nthSpine : Nat → Expr → Option Expr
  | 0, .con2 c h _ => if c = consTag then some h else none
  | n + 1, .con2 c _ t => if c = consTag then nthSpine n t else none
  | _, _ => none

/-- Navigate a quotation along a path: the node value at the path's end, or
`none` when the path does not address one. A leaf node is unwrapped and a struct
or array node is descended into by its own tag. -/
def nav {d : Layout} : (p : Path d) → Expr → Option Expr
  | .here, v => some v
  | .left q, v =>
      match unwrapNode v with
      | .con2 c x _ => if c = structTag then nav q x else none
      | _ => none
  | .right q, v =>
      match unwrapNode v with
      | .con2 c _ y => if c = structTag then nav q y else none
      | _ => none
  | .index i q, v => (nthSpine i (unwrapNode v)).bind (fun e => nav q e)

/-- Navigating a spine is reading the list: the `i`-th element's node, or
nothing when the spine is shorter. -/
theorem nthSpine_spineVal : ∀ {a : Layout} (i : Nat) (l : List (State a)),
    nthSpine i (spineVal a l) = (l[i]?).map (cellVal a)
  | _, 0, [] => by simp [spineVal, nthSpine, nilTag]
  | _, 0, x :: t => by simp [spineVal, nthSpine, consTag]
  | _, n + 1, [] => by simp [spineVal, nthSpine, nilTag]
  | _, n + 1, x :: t => by
      simp [spineVal, nthSpine, consTag, nthSpine_spineVal n t]

/-- A struct node is its own unwrapped node. -/
theorem unwrapNode_struct {a b : Layout} (u : State a) (v : State b) :
    unwrapNode (.con2 structTag (cellVal a u) (cellVal b v)) =
      .con2 structTag (cellVal a u) (cellVal b v) := by
  simp [unwrapNode, structTag]

/-- A spine is its own unwrapped node. -/
theorem unwrapNode_spine {a : Layout} (l : List (State a)) :
    unwrapNode (spineVal a l) = spineVal a l := by
  cases l with
  | nil => simp [spineVal, unwrapNode, nilTag]
  | cons x t => simp [spineVal, unwrapNode, consTag]

/-- Navigating a state's quotation along an in-bounds path is the quotation of
the state's own node there: the path-resolution law. -/
theorem nav_cellVal (d : Layout) (s : State d) : ∀ (p : Path d), InBounds p s →
    nav p (cellVal d s) = some (nodeVal p s) := by
  intro p
  induction p with
  | here => intro _; rfl
  | left q ih =>
      intro hb
      obtain ⟨u, v⟩ := s
      rw [cellVal_struct]
      simp only [nav]
      rw [unwrapNode_struct]
      simp only [structTag, reduceIte]
      rw [show nodeVal (.left q) (u, v) = nodeVal q u from rfl]
      exact ih u hb
  | right q ih =>
      intro hb
      obtain ⟨u, v⟩ := s
      rw [cellVal_struct]
      simp only [nav]
      rw [unwrapNode_struct]
      simp only [structTag, reduceIte]
      rw [show nodeVal (.right q) (u, v) = nodeVal q v from rfl]
      exact ih v hb
  | index i q ih =>
      intro hb
      obtain ⟨e, he, hb⟩ := hb
      rw [cellVal_arr]
      have hli : s.toList[i]? = some e := by rw [Array.getElem?_toList]; exact he
      simp only [nav, unwrapNode_spine, nthSpine_spineVal, hli, Option.map_some,
        Option.bind_some, nodeVal]
      rw [subAt_index, he]
      exact ih e hb

end TreeOwnership

end Scidonia.RC
