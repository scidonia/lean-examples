# Fractional permissions

## The question
- Lean values are immutable, yet `Array.set!` updates in place when the array's reference count is 1.
- So if we are careful to keep only one reference, we get update in place. But ==how do we know we only have one reference?==
- If we could enforce that, we would have mutable programming in a pure language.
- We want a discipline over one shared object: ==writes need exclusive access, reads may share==.
- And we want the type checker to enforce it, at no cost at run time.

## Fractional permissions
- Boyland (2003): a permission is a *fraction* of an object.
- A write needs the whole, `1`. A read takes any positive share; shares split, and sum back.
- Once every read is returned, the shares sum to `1` again and writing is allowed.
- Separation logics — Iris, VeriFast, Viper, F* Pulse — reason about memory exactly this way.

## Lean has no linear types
- A token value can always be copied: `let t' := t`.
- So the permission cannot live in the token. It lives in a ==ghost ledger== of `(id, fraction)` entries.
- A token is only a *name* for an entry: a copy is a second name, not a second permission.
- The ledger appears only in types and proofs, so the compiler erases it.

```the ledger
import Scidonia.FracPerm
open Scidonia.FracPerm

-- Outstanding reads: (ghost id, fraction).
example : Ledger = List (Nat × Rat) := rfl

-- Two reads out, a third and two thirds: nothing is held.
example : Ledger.held [(0, 1/3), (1, 2/3)] = 0 := by
  simp [Ledger.held]; grind

-- Returning an entry gives back exactly its fraction.
example {n : Nat} {q : Rat} {l : Ledger} (h : (n, q) ∈ l) :
    Ledger.held (l.erase (n, q)) = Ledger.held l + q :=
  Ledger.held_erase_of_mem h
```

## A Hoare monad over the object
- `HSt σ P β Q`: a program over a state `σ`, whose precondition `P` and postcondition `Q` speak about the ledger and the state.
- `acquire n q` needs a fresh id and `0 < q ≤ held`. `read` and `release` need the token's entry. `write` needs `held = 1`.
- `exec` starts from the empty ledger and demands a proof that the program ends with `held = 1`: ==every fraction returned exactly once==.

```a program
import Scidonia.FracPerm
open Scidonia.FracPerm HSt

def twoReaders :=
  acquire (σ := Array Nat) 0 (1 / 3) >>>= fun t₁ =>
  acquire 1 (2 / 3) >>>= fun t₂ =>
  read t₁ 0 >>>= fun v =>
  release t₁ >>>= fun _ =>
  release t₂ >>>= fun _ =>
  write (0, 9) >>>= fun _ => ret v

#guard twoReaders.exec #[7] (by hst_vc) (by hst_vc)
  == (some 7, #[9])
```

## The structure of FracPerm
- `Ledger := List (Nat × Rat)`; `held l = 1 - (sum of the fractions)` is what the program has left to lend.
- `ReadTok n q`: a field-less token, constructor private, indexed by its ledger entry.
- `HSt σ P β Q`: a structure whose private constructor and private `run` field hold a function from a state and a proof of `P` to a result, a new state and a proof of `Q`.
- `run` also demands `Cap`, a private `Prop`: `exec` is the only way in.

```the program type
import Scidonia.FracPerm
open Scidonia.FracPerm HSt

example (l : Ledger) :
    l.held = 1 - (l.map Prod.snd).sum := rfl

variable {σ R W : Type} [FracObject σ R W]

example : Pre σ = (Ledger → σ → Prop) := rfl
example (β : Type) :
    Post σ β = (Ledger → σ → β → Ledger → σ → Prop) := rfl

example {β : Type} {P : Pre σ} {Q : Post σ β}
    (m : HSt σ P β Q) (s : σ) (hp : P [] s)
    (hq : ∀ b l' s', Q [] s b l' s' → l'.held = 1) : β × σ :=
  m.exec s hp hq
```

## The primitives
- Each primitive's precondition and postcondition are in its type.
- `bind` (`>>>=`) composes them: the first postcondition must establish the second precondition.

```specifications
import Scidonia.FracPerm
open Scidonia.FracPerm HSt

variable {σ R W : Type} [FracObject σ R W]

example (n : Nat) (q : Rat) :
    HSt σ (fun l _ => n ∉ l.map Prod.fst ∧ 0 < q ∧ q ≤ l.held)
      (ReadTok n q) (fun l s _ l' s' => l' = (n, q) :: l ∧ s' = s) :=
  acquire n q

example {n : Nat} {q : Rat} (t : ReadTok n q) :
    HSt σ (fun l _ => (n, q) ∈ l) Unit
      (fun l s _ l' s' => l' = l.erase (n, q) ∧ s' = s) :=
  release t

example (o : W) :
    HSt σ (fun l _ => l.held = 1) Unit
      (fun l s _ l' s' => l' = l ∧ s' = FracObject.update o s) :=
  write o
```
