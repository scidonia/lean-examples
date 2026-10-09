/-
A Hoare monad over an `Array` whose reads are tracked by fractional
permissions in an erased ghost ledger.

The caller never touches the array. A program is an `HArr` value, whose
constructor is private, so the only way to obtain one is through the
primitives of this module. The specification (`Pre`/`Post`) mentions the ghost
`Ledger` of `Scidonia.FracPerm.Ledger`, but both are specification-only: a
`Pre` is a `Prop`-valued function and the ledger appears in a program's type
and in its proofs. The ledger and every proof — including the `Cap` that `run`
demands — are erased, showing up as `◾`, so the only state a compiled client
program threads is the `Array α`; tokens are the one other run-time value (below).

A `ReadTok` is not erased, because `ReadTok n q` is a `Type`. It is a
field-less structure and compiles to a constant scalar (`ctor_0`, the same
representation as `Unit`): a token allocates nothing, is not reference
counted, and carries neither the id nor the fraction.

The ghost id `n` and the fraction `q` are ordinary `Nat` and `Rat` arguments,
and Lean erases arguments by their type — proofs, types and type formers — not
by whether the body uses them. Written out literally they are dropped by the
compiler's arity reduction, and `HArr.acquire` becomes `HArr.acquire._redArg`,
whose lambda takes the array and an erased proof; a caller that computes them,
say `generic (k * 7) (r / 2)`, does not evaluate them either, because the call
goes through the same reduced entry. A definition that is generic in `n` and
`q` keeps them in its own compiled signature as unused `@&` parameters, and
its `_boxed` entry takes them boxed, so a use that arity reduction cannot
reach — a call through a function value, for instance — has to compute and box
them.

The permission discipline is:

* `write` requires the caller to hold the whole array (`held = 1`).
* `acquire n q` lends out a fraction `0 < q ≤ held`, naming it with a fresh
  ghost id, and returns a `ReadTok n q`.
* `read` needs its token's ledger entry to still be present; any number of
  reads may be outstanding at once, and the same token may be used for
  several reads.
* `release` gives back exactly the fraction `q` and removes the entry.

Tokens are values and may be copied, so enforcement does not come from
linearity. It comes from the ghost ledger: a copy of `ReadTok n q` is usable
only while `(n, q)` is an entry of the ledger, and `release` removes that
entry, so a second `release` of the same token (or a `read` with it) has a
false precondition. Once every entry is returned the held fraction is back to
`1` and `write` is available again.

`exec` runs a program from the empty ledger and demands a proof that the
program ends with every fraction returned, i.e. with `held = 1`.

Compiled, a program threads one reference-counted array, and `set!` updates
that object in place only while the program's reference to it is exclusive; a
shared array is copied instead. `Scidonia.FracPerm.InPlace` makes that
difference observable — and, at the option of the process environment,
fatal — without appearing in any specification or proof.
-/
import Scidonia.FracPerm.Ledger
import Scidonia.FracPerm.InPlace

namespace Scidonia.FracPerm

/-- A token standing for one outstanding read of fraction `q`, carrying the
ghost id `n` of the ledger entry that entitles its holder to the fraction.
Its constructor is private: tokens cannot be forged, only `acquire` makes
them. Since the id and the fraction are type indices, a token has no fields:
it compiles to a constant scalar (`ctor_0`, as `Unit` does), allocates
nothing, and carries neither the id nor the fraction. -/
structure ReadTok (n : Nat) (q : Rat) : Type where
  private mk ::

/-- A precondition: for every ledger and array, the configuration in which a
program may start. -/
abbrev Pre (α : Type) := Ledger → Array α → Prop

/-- A postcondition: relating the starting configuration and result to the
final ledger and array. -/
abbrev Post (α β : Type) := Ledger → Array α → β → Ledger → Array α → Prop

/-- The capability to run a program. Its only constructor is private to this
module, so a client can obtain no value of it: `run` demands one, which is
what makes `exec` the only entry point even though a structure's eliminators
expose the accessor's type. Being a `Prop`, the capability is erased and
costs nothing at run time. -/
private structure Cap : Prop where
  mk ::

/-- A program over an `Array α` with precondition `P` and postcondition `Q`.
The constructor is private, so client code cannot build a program out of
thin air, and the accessor demands a `Cap`, which only this module can
produce. A client therefore cannot choose the ledger a program starts from —
not through `run` and not through the eliminators that expose it — and the
only entry point from outside the module is `exec`, which starts at the
empty ledger and demands a proof that the program ends holding the whole
array. -/
structure HArr (α : Type) (P : Pre α) (β : Type) (Q : Post α β) where
  private mk ::
  /-- Run the program on an array, given a proof that some ledger meets the
  precondition. Private to this module, and usable only with a `Cap`:
  `exec` is the entry point. -/
  private run : Cap → (a : Array α) → (∃ l, P l a) →
    { r : β × Array α // ∀ l, P l a → ∃ l', Q l a r.1 l' r.2 }

namespace HArr

/-- The precondition a program's type records. -/
abbrev pre {α β : Type} {P : Pre α} {Q : Post α β} (_m : HArr α P β Q) : Pre α := P

/-- The postcondition a program's type records. -/
abbrev post {α β : Type} {P : Pre α} {Q : Post α β} (_m : HArr α P β Q) : Post α β := Q

/-- The program that returns `b` and leaves both ledger and array alone. -/
def ret (b : β) : HArr α (fun _ _ => True) β (fun l a b' l' a' => l' = l ∧ a' = a ∧ b' = b) :=
  ⟨fun _ a _ => ⟨(b, a), fun l _ => ⟨l, rfl, rfl, rfl⟩⟩⟩

/-- Sequence two programs: the first's postcondition must establish the
second's precondition, and the combined postcondition is the composition of
the two. -/
def bind {P₁ : Pre α} {Q₁ : Post α β} {P₂ : β → Pre α} {Q₂ : β → Post α γ}
    (m : HArr α P₁ β Q₁) (f : (x : β) → HArr α (P₂ x) γ (Q₂ x)) :
    HArr α (fun l a => P₁ l a ∧ ∀ x l' a', Q₁ l a x l' a' → P₂ x l' a') γ
      (fun l a y l'' a'' => ∃ x l' a', Q₁ l a x l' a' ∧ Q₂ x l' a' y l'' a'') :=
  ⟨fun _ a h =>
    let ⟨(x, a'), hm⟩ := m.run ⟨⟩ a (h.elim fun l hl => ⟨l, hl.1⟩)
    let ⟨(y, a''), hf⟩ := (f x).run ⟨⟩ a' (h.elim fun l hl =>
      (hm l hl.1).elim fun l' hq => ⟨l', hl.2 x l' a' hq⟩)
    ⟨(y, a''), fun l hl => (hm l hl.1).elim fun l' hq =>
      (hf l' (hl.2 x l' a' hq)).elim fun l'' hq' => ⟨l'', x, l', a', hq, hq'⟩⟩⟩

/-- Weaken a program's specification: a stronger precondition and a weaker
postcondition are both sound. -/
def conseq {P P' : Pre α} {Q Q' : Post α β} (m : HArr α P β Q)
    (hpre : ∀ l a, P' l a → P l a) (hpost : ∀ l a b l' a', Q l a b l' a' → Q' l a b l' a') :
    HArr α P' β Q' :=
  ⟨fun _ a h => by
    obtain ⟨r, hr⟩ := m.run ⟨⟩ a (h.elim fun l hl => ⟨l, hpre l a hl⟩)
    exact ⟨r, fun l hl' => (hr l (hpre l a hl')).elim fun l'' hq => ⟨l'', hpost l a r.1 l'' r.2 hq⟩⟩⟩

/-- Lend out the fraction `q` of the array under the fresh ghost id `n`, and
hand back the token that entitles its holder to read with it. Freshness of
`n` is what makes each `release` give back exactly one fraction: the ledger
carries at most one entry per id.

The token has no fields and compiles to a constant scalar (`ctor_0`, as `Unit`
does): no allocation, no reference counting, and it carries neither the id nor
the fraction, while the specifications are proofs and are erased. The id and
the fraction are ordinary arguments; see the module note for what the compiler
does with them. -/
def acquire (n : Nat) (q : Rat) :
    HArr α (fun l _ => n ∉ l.map Prod.fst ∧ 0 < q ∧ q ≤ l.held) (ReadTok n q)
      (fun l a _ l' a' => l' = (n, q) :: l ∧ a' = a) :=
  ⟨fun _ a _ => ⟨(⟨⟩, a), fun _ _ => ⟨_, rfl, rfl⟩⟩⟩

/-- Read index `i`, returning `a[i]?`. Only a holder of a token whose ledger
entry is still present may do so; reading changes nothing. -/
def read {n : Nat} {q : Rat} (_t : ReadTok n q) (i : Nat) :
    HArr α (fun l _ => (n, q) ∈ l) (Option α)
      (fun l a v l' a' => l' = l ∧ a' = a ∧ v = a[i]?) :=
  ⟨fun _ a _ => ⟨(a[i]?, a), fun l _ => ⟨l, rfl, rfl, rfl⟩⟩⟩

/-- Give the fraction `q` back and consume the token's ledger entry. A second
`release` of the same token is rejected: the entry is gone, and a `read` with
it is rejected for the same reason. -/
def release {n : Nat} {q : Rat} (_t : ReadTok n q) :
    HArr α (fun l _ => (n, q) ∈ l) Unit
      (fun l a _ l' a' => l' = l.erase (n, q) ∧ a' = a) :=
  ⟨fun _ a _ => ⟨((), a), fun _ _ => ⟨_, rfl, rfl⟩⟩⟩

/-- Write `v` to index `i`. Requires the caller to hold the whole array: some
entry is outstanding in every other case.

The write guards its array with `assertExclusive`, the identity in the logic
and a run-time check of ownership in the compiled program; see
`Scidonia.FracPerm.InPlace`. -/
def write (i : Nat) (v : α) :
    HArr α (fun l _ => l.held = 1) Unit (fun l a _ l' a' => l' = l ∧ a' = a.set! i v) :=
  ⟨fun _ a _ =>
      ⟨((), (assertExclusive "Scidonia.FracPerm.HArr.write" a).set! i v),
        fun l _ => ⟨l, rfl, rfl⟩⟩⟩

/-- Run a program from the empty ledger. The result of the program is only
available to a caller who can prove the program still holds the whole array
at the end, i.e. that every fraction taken out was returned. -/
def exec (m : HArr α P β Q) (a : Array α) (hp : P [] a)
    (_hq : ∀ b l' a', Q [] a b l' a' → l'.held = 1) : β × Array α :=
  (m.run ⟨⟩ a ⟨[], hp⟩).1

end HArr

/-- Left-associative sequencing of programs. -/
infixl:55 " >>>= " => HArr.bind

open HArr

/-- Discharge the verification conditions that `exec` leaves behind: the
program's precondition at the empty ledger, and the closing obligation that
the held fraction is `1`. -/
macro "harr_vc" : tactic => `(tactic| (simp [Ledger.held] at * <;> grind))

end Scidonia.FracPerm
