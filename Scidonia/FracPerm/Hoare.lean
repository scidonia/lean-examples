/-
A Hoare monad over a state of any type, whose reads are tracked by fractional
permissions in an erased ghost ledger.

An object joins the interface by an instance of `FracObject`: the instance
names the object's read and write operation types, says how a read operation
is performed (`observe`) and how a write operation is performed (`update`),
and supplies the in-place check `write` runs before an update (`check`, the
identity in the logic). An object of the interface's own is the `Array`
instance below; `Scidonia.FracPerm.Counter` is a worked second one.

The caller never touches the state. A program is an `HSt` value, whose
constructor is private, so the only way to obtain one is through the primitives
of this module. The specification (`Pre`/`Post`) mentions the ghost `Ledger` of
`Scidonia.FracPerm.Ledger`, but both are specification-only: a `Pre` is a
`Prop`-valued function and the ledger appears in a program's type and in its
proofs. The ledger and every proof — including the `Cap` that `run` demands —
are erased, showing up as `◾`, so the only state a compiled client program
threads is the object itself; tokens are the one other run-time value (below).

A `ReadTok` is not erased, because `ReadTok n q` is a `Type`. It is a
field-less structure and compiles to a constant scalar (`ctor_0`, the same
representation as `Unit`): a token allocates nothing, is not reference
counted, and carries neither the id nor the fraction.

The ghost id `n` and the fraction `q` are ordinary `Nat` and `Rat` arguments,
and Lean erases arguments by their type — proofs, types and type formers — not
by whether the body uses them. Written out literally they are dropped by the
compiler's arity reduction, and `HSt.acquire` becomes `HSt.acquire._redArg`,
whose lambda takes the state and an erased proof; a caller that computes them,
say `generic (k * 7) (r / 2)`, does not evaluate them either, because the call
goes through the same reduced entry. A definition that is generic in `n` and
`q` keeps them in its own compiled signature as unused `@&` parameters, and
its `_boxed` entry takes them boxed, so a use that arity reduction cannot
reach — a call through a function value, for instance — has to compute and box
them.

The permission discipline is:

* `write o` requires the caller to hold the whole state (`held = 1`).
* `acquire n q` lends out a fraction `0 < q ≤ held`, naming it with a fresh
  ghost id, and returns a `ReadTok n q`.
* `read t o` needs its token's ledger entry to still be present; any number of
  reads may be outstanding at once, and the same token may be used for
  several reads.
* `release` gives back exactly the fraction `q` and removes the entry.
* `withRead n q body` is `acquire`, run `body`, `release`, and return the
  body's result: the scope returns the fraction no matter how `body` ends, so
  the caller cannot leak it and needs no `release` of its own.

Tokens are values and may be copied, so enforcement does not come from
linearity. It comes from the ghost ledger: a copy of `ReadTok n q` is usable
only while `(n, q)` is an entry of the ledger, and `release` removes that
entry, so a second `release` of the same token (or a `read` with it) has a
false precondition. Once every entry is returned the held fraction is back to
`1` and `write` is available again.

`exec` runs a program from the empty ledger and demands a proof that the
program ends with every fraction returned, i.e. with `held = 1`.

Compiled, a program threads one reference-counted object, and an in-place
update mutates that object only while the program's reference to it is
exclusive; a shared object is copied instead. `Scidonia.FracPerm.InPlace` makes
that difference observable — and, at the option of the process environment,
fatal — without appearing in any specification or proof.
-/
import Scidonia.FracPerm.Ledger
import Scidonia.FracPerm.InPlace

namespace Scidonia.FracPerm

/-- What an object offers the fractional-permission monad: the types of its
read and write operations, how it is read, how it is written, and the in-place
check `write` runs before an update.

The two operation types are `outParam`s rather than fields. `read` and `write`
take an operation of the object's own type, and a program names its object once
and lets the rest be typed from it, so the elaborator must obtain the operation
types from the object alone. A class *field* cannot do that: an argument whose
expected type is a projection of the class — `FracObject.ReadOp σ` — is not
reducible until that projection's own instance argument is known, and instance
search does not resolve a nested class goal to reduce an argument type. A
literal such as the array's `0`, or the pair `(0, 7)`, then has no type at all
and cannot be given as an operation. Naming the types as parameters lets
instance resolution assign them while it finds the object's instance.

`Result` makes the read operations heterogeneous: a read operation may yield a
value of any type, one per operation, so an object can offer a plain field and
an indexed field through the one `read`.

Instances must respect two rules that no specification can state, because they
are about the run-time representation of the values rather than about their
mathematics:

* `observe` must not return a reference to a part of the state that some write
  updates in place. A read that hands back the array field of a structure, say,
  leaves an alias behind, and the next `update` of that field copies it.
  Sharing values that no write mutates in place — a `Nat`, or an element's own
  value — is harmless and expected; it is the state's mutable parts that a
  read's result must not name.
* `update` must not keep an old part of the state alive. `{ s with f := … }`
  writes one field in place; building the new state around a copy of the old
  parts makes the next update copy them.

Neither is checkable from the specifications, which is why the interface says
it in prose and why the check hook exists at all. -/
class FracObject (σ : Type) (ReadOp : outParam Type) (WriteOp : outParam Type) where
  /-- The value a read operation yields. -/
  Result : ReadOp → Type
  /-- Perform a read operation. -/
  observe : (o : ReadOp) → σ → Result o
  /-- Perform a write operation. -/
  update : WriteOp → σ → σ
  /-- The check `write` runs before `update`, given the site, the operation
  about to run and the state it is about to run on.

  It is the identity in the logic, so no specification or proof mentions it; a
  law (`check_eq`) rather than a definitional equation, because an instance is
  free to define it as compilation-only (an identity definition with an
  `implemented_by` implementation), and its compiled form is what makes a
  copying update loud.

  It defaults to `assertExclusive` on the whole object. An object whose mutable
  state is a field of a larger object — a structure with an array field, say —
  replaces the default with a check of that field, so that the copy the field
  would take is caught; the operation is a parameter so that such a check can
  leave alone what the operation does not write. -/
  check : String → WriteOp → σ → σ := fun site _ s => assertExclusive site s
  /-- `check` is the identity: `check site o s = s`. An instance whose `check`
  is an identity definition with an `implemented_by` implementation proves this
  by `rfl`. -/
  check_eq : ∀ site o s, check site o s = s

/-- The `Array` instance: a read operation is an index and yields `a[i]?`, and
a write operation is an index and a value and sets the one element. Its
behaviour is the array interface's, unchanged: the same `set!` on the same
object, and a check that names the array's size in its report. -/
instance instFracObjectArray (α : Type) : FracObject (Array α) Nat (Nat × α) where
  Result := fun _ => Option α
  observe := fun i a => a[i]?
  update := fun iv a => a.set! iv.1 iv.2
  check := fun site _ a => assertExclusiveArray site a
  check_eq := fun _ _ _ => rfl

/-- A token standing for one outstanding read of fraction `q`, carrying the
ghost id `n` of the ledger entry that entitles its holder to the fraction.
Its constructor is private: tokens cannot be forged, only `acquire` makes
them. Since the id and the fraction are type indices, a token has no fields:
it compiles to a constant scalar (`ctor_0`, as `Unit` does), allocates
nothing, and carries neither the id nor the fraction. -/
structure ReadTok (n : Nat) (q : Rat) : Type where
  private mk ::

/-- A precondition: for every ledger and state, the configuration in which a
program may start. -/
abbrev Pre (σ : Type) := Ledger → σ → Prop

/-- A postcondition: relating the starting configuration and result to the
final ledger and state. -/
abbrev Post (σ β : Type) := Ledger → σ → β → Ledger → σ → Prop

/-- The capability to run a program. Its only constructor is private to this
module, so a client can obtain no value of it: `run` demands one, which is
what makes `exec` the only entry point even though a structure's eliminators
expose the accessor's type. Being a `Prop`, the capability is erased and
costs nothing at run time. -/
private structure Cap : Prop where
  mk ::

/-- A program over a state of type `σ` with precondition `P` and postcondition
`Q`. The constructor is private, so client code cannot build a program out of
thin air, and the accessor demands a `Cap`, which only this module can
produce. A client therefore cannot choose the ledger a program starts from —
not through `run` and not through the eliminators that expose it — and the
only entry point from outside the module is `exec`, which starts at the
empty ledger and demands a proof that the program ends holding the whole
state. -/
structure HSt (σ : Type) (P : Pre σ) (β : Type) (Q : Post σ β) where
  private mk ::
  /-- Run the program on a state, given a proof that some ledger meets the
  precondition. Private to this module, and usable only with a `Cap`:
  `exec` is the entry point. -/
  private run : Cap → (s : σ) → (∃ l, P l s) →
    { r : β × σ // ∀ l, P l s → ∃ l', Q l s r.1 l' r.2 }

namespace HSt

/-- The precondition a program's type records. -/
abbrev pre {σ β : Type} {P : Pre σ} {Q : Post σ β} (_m : HSt σ P β Q) : Pre σ := P

/-- The postcondition a program's type records. -/
abbrev post {σ β : Type} {P : Pre σ} {Q : Post σ β} (_m : HSt σ P β Q) : Post σ β := Q

/-- The program that returns `b` and leaves both ledger and state alone. -/
def ret (b : β) : HSt σ (fun _ _ => True) β (fun l s b' l' s' => l' = l ∧ s' = s ∧ b' = b) :=
  ⟨fun _ s _ => ⟨(b, s), fun l _ => ⟨l, rfl, rfl, rfl⟩⟩⟩

/-- Sequence two programs: the first's postcondition must establish the
second's precondition, and the combined postcondition is the composition of
the two. -/
def bind {P₁ : Pre σ} {Q₁ : Post σ β} {P₂ : β → Pre σ} {Q₂ : β → Post σ γ}
    (m : HSt σ P₁ β Q₁) (f : (x : β) → HSt σ (P₂ x) γ (Q₂ x)) :
    HSt σ (fun l s => P₁ l s ∧ ∀ x l' s', Q₁ l s x l' s' → P₂ x l' s') γ
      (fun l s y l'' s'' => ∃ x l' s', Q₁ l s x l' s' ∧ Q₂ x l' s' y l'' s'') :=
  ⟨fun _ s h =>
    let ⟨(x, s'), hm⟩ := m.run ⟨⟩ s (h.elim fun l hl => ⟨l, hl.1⟩)
    let ⟨(y, s''), hf⟩ := (f x).run ⟨⟩ s' (h.elim fun l hl =>
      (hm l hl.1).elim fun l' hq => ⟨l', hl.2 x l' s' hq⟩)
    ⟨(y, s''), fun l hl => (hm l hl.1).elim fun l' hq =>
      (hf l' (hl.2 x l' s' hq)).elim fun l'' hq' => ⟨l'', x, l', s', hq, hq'⟩⟩⟩

/-- Weaken a program's specification: a stronger precondition and a weaker
postcondition are both sound. -/
def conseq {P P' : Pre σ} {Q Q' : Post σ β} (m : HSt σ P β Q)
    (hpre : ∀ l s, P' l s → P l s) (hpost : ∀ l s b l' s', Q l s b l' s' → Q' l s b l' s') :
    HSt σ P' β Q' :=
  ⟨fun _ s h => by
    obtain ⟨r, hr⟩ := m.run ⟨⟩ s (h.elim fun l hl => ⟨l, hpre l s hl⟩)
    exact ⟨r, fun l hl' => (hr l (hpre l s hl')).elim fun l'' hq => ⟨l'', hpost l s r.1 l'' r.2 hq⟩⟩⟩

/-- Lend out the fraction `q` of the state under the fresh ghost id `n`, and
hand back the token that entitles its holder to read with it. Freshness of
`n` is what makes each `release` give back exactly one fraction: the ledger
carries at most one entry per id.

The token has no fields and compiles to a constant scalar (`ctor_0`, as `Unit`
does): no allocation, no reference counting, and it carries neither the id nor
the fraction, while the specifications are proofs and are erased. The id and
the fraction are ordinary arguments; see the module note for what the compiler
does with them. -/
def acquire (n : Nat) (q : Rat) :
    HSt σ (fun l _ => n ∉ l.map Prod.fst ∧ 0 < q ∧ q ≤ l.held) (ReadTok n q)
      (fun l s _ l' s' => l' = (n, q) :: l ∧ s' = s) :=
  ⟨fun _ s _ => ⟨(⟨⟩, s), fun _ _ => ⟨_, rfl, rfl⟩⟩⟩

/-- Read operation `o`, yielding the value `observe o s`. Only a holder of a
token whose ledger entry is still present may do so; reading changes
nothing. -/
def read [FracObject σ ReadOp WriteOp] {n : Nat} {q : Rat} (_t : ReadTok n q) (o : ReadOp) :
    HSt σ (fun l _ => (n, q) ∈ l) (FracObject.Result (σ := σ) o)
      (fun l s v l' s' => l' = l ∧ s' = s ∧ v = FracObject.observe o s) :=
  ⟨fun _ s _ => ⟨(FracObject.observe o s, s), fun l _ => ⟨l, rfl, rfl, rfl⟩⟩⟩

/-- Give the fraction `q` back and consume the token's ledger entry. A second
`release` of the same token is rejected: the entry is gone, and a `read` with
it is rejected for the same reason. -/
def release {n : Nat} {q : Rat} (_t : ReadTok n q) :
    HSt σ (fun l _ => (n, q) ∈ l) Unit
      (fun l s _ l' s' => l' = l.erase (n, q) ∧ s' = s) :=
  ⟨fun _ s _ => ⟨((), s), fun _ _ => ⟨_, rfl, rfl⟩⟩⟩

/-- Write with operation `o`. Requires the caller to hold the whole state: some
entry is outstanding in every other case.

Before the update, the object's `check` runs on the operation and the state.
It is the identity in the logic — `check_eq` is what lets the postcondition
speak of `update o s` alone — and its compiled form is the in-place check; see
`Scidonia.FracPerm.InPlace` and `FracObject.check`. -/
def write [FracObject σ ReadOp WriteOp] (o : WriteOp) :
    HSt σ (fun l _ => l.held = 1) Unit
      (fun l s _ l' s' => l' = l ∧ s' = FracObject.update o s) :=
  ⟨fun _ s _ =>
      ⟨((), FracObject.update o (FracObject.check "Scidonia.FracPerm.HSt.write" o s)),
        fun l _ => ⟨l, rfl,
          congrArg (FracObject.update o) (FracObject.check_eq _ o s)⟩⟩⟩

/-- Read under a scope: lend out `(n, q)`, run `body` with the token, give the
fraction back, and return the body's result. `body` cannot leak the fraction —
the scope's own `release` gives it back — and a `release` of `t` inside `body`
is rejected, because the scope's `release` then finds the entry gone.

It is built from `acquire`, `bind`, `release` and `ret`, so it adds no trust:
the specification below is a consequence of theirs, proved by `conseq`, and
`body`'s own precondition and postcondition are those the caller writes. -/
def withRead {σ : Type} {β : Type} {P : Pre σ} {Q : Post σ β}
    (n : Nat) (q : Rat) (body : (t : ReadTok n q) → HSt σ P β Q) :
    HSt σ
      (fun l s =>
        (n ∉ l.map Prod.fst ∧ 0 < q ∧ q ≤ l.held) ∧
          ∀ l₁ s₁, l₁ = (n, q) :: l ∧ s₁ = s →
            P l₁ s₁ ∧ ∀ b l₂ s₂, Q l₁ s₁ b l₂ s₂ → (n, q) ∈ l₂)
      β
      (fun l s b l' s' => ∃ l₁ s₁ b' l₂ s₂,
        l₁ = (n, q) :: l ∧ s₁ = s ∧ Q l₁ s₁ b' l₂ s₂ ∧
        l' = l₂.erase (n, q) ∧ s' = s₂ ∧ b = b') :=
  (HSt.bind (acquire n q) fun t =>
    HSt.bind (body t) fun b =>
    HSt.bind (release t) fun _ => ret b).conseq
    (by
      intro l s h
      refine ⟨h.1, ?_⟩
      intro _ l₁ s₁ h'
      exact ⟨(h.2 l₁ s₁ h').1,
        fun b l₂ s₂ hQ => ⟨(h.2 l₁ s₁ h').2 b l₂ s₂ hQ, fun _ _ _ _ => trivial⟩⟩)
    (fun _ _ _ _ _ h => by
      obtain ⟨_, l₁, s₁, h1, h2⟩ := h
      obtain ⟨b', l₂, s₂, hQ, h3⟩ := h2
      obtain ⟨_, l₃, s₃, h4, h5⟩ := h3
      exact ⟨l₁, s₁, b', l₂, s₂, h1.1, h1.2, hQ,
        h5.1.trans h4.1, h5.2.1.trans h4.2, h5.2.2⟩)

/-- Run a program from the empty ledger. The result of the program is only
available to a caller who can prove the program still holds the whole state
at the end, i.e. that every fraction taken out was returned. -/
def exec (m : HSt σ P β Q) (s : σ) (hp : P [] s)
    (_hq : ∀ b l' s', Q [] s b l' s' → l'.held = 1) : β × σ :=
  (m.run ⟨⟩ s ⟨[], hp⟩).1

end HSt

/-- Left-associative sequencing of programs. -/
infixl:55 " >>>= " => HSt.bind

open HSt

/-- Discharge the verification conditions that `exec` leaves behind: the
program's precondition at the empty ledger, and the closing obligation that
the held fraction is `1`. -/
macro "hst_vc" : tactic => `(tactic| (simp [Ledger.held] at * <;> grind))

end Scidonia.FracPerm
