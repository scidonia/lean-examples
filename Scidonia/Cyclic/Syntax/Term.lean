import Scidonia.Cyclic.Syntax.StrictPos

namespace Scidonia
namespace Cyclic
namespace Syntax

/-- Core dependently-typed term syntax (CoC/CIC-flavoured).

We use de Bruijn indices for variables.

This is intentionally close to the Coq development in `../cyclic/theories/Syntax/Term.v`:
- `sort i` is `Type i` (we keep just `Nat` levels for now)
- `pi A B` and `lam A t` bind one variable in the second component
- `fix A t` is general recursion
- inductives are referenced by indices into a global environment
- `roll`/`case` implement constructors and pattern matching
-/
inductive Tm : Type
  | var : Nat → Tm
  | sort : Nat → Tm
  | pi : Tm → Tm → Tm
  | lam : Tm → Tm → Tm
  | app : Tm → Tm → Tm
  | fix : Tm → Tm → Tm
  | ind : Nat → Tm
  | roll : (I : Nat) → (c : Nat) → (params recs : List Tm) → Tm
  | case : (I : Nat) → (scrut : Tm) → (C : Tm) → (brs : List Tm) → Tm

namespace Tm

def branch (brs : List Tm) (c : Nat) : Option Tm :=
  brs[c]?

def size : Tm → Nat
  | var _ => 1
  | sort _ => 1
  | pi A B => 1 + size A + size B
  | lam A t => 1 + size A + size t
  | app t u => 1 + size t + size u
  | fix A t => 1 + size A + size t
  | ind _ => 1
  | roll _ _ params recs =>
      1 + params.foldr (fun u n => size u + n) 0 + recs.foldr (fun u n => size u + n) 0
  | case _ scrut C brs =>
      1 + size scrut + size C + brs.foldr (fun u n => size u + n) 0

/-- Renaming under a binder. -/
def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | x + 1 => ρ x + 1

/-- Capture-avoiding renaming. -/
def rename (ρ : Nat → Nat) : Tm → Tm
  | var x => var (ρ x)
  | sort i => sort i
  | pi A B => pi (rename ρ A) (rename (upRen ρ) B)
  | lam A t => lam (rename ρ A) (rename (upRen ρ) t)
  | app t u => app (rename ρ t) (rename ρ u)
  | fix A t => fix (rename ρ A) (rename (upRen ρ) t)
  | ind I => ind I
  | roll I c params recs =>
      roll I c (params.map (rename ρ)) (recs.map (rename ρ))
  | case I scrut C brs =>
      case I (rename ρ scrut) (rename ρ C) (brs.map (rename ρ))

/-- Shifts all free variables `x ≥ c` by `d`. -/
def shiftSub (d c : Nat) : Nat → Nat :=
  fun x => if x < c then x else x + d

def shift (d c : Nat) (t : Tm) : Tm :=
  rename (shiftSub d c) t

/-- Lifts a substitution under a binder. -/
def upSub (σ : Nat → Tm) : Nat → Tm
  | 0 => var 0
  | x + 1 => shift 1 0 (σ x)

/-- Capture-avoiding substitution. -/
def subst (σ : Nat → Tm) : Tm → Tm
  | var x => σ x
  | sort i => sort i
  | pi A B => pi (subst σ A) (subst (upSub σ) B)
  | lam A t => lam (subst σ A) (subst (upSub σ) t)
  | app t u => app (subst σ t) (subst σ u)
  | fix A t => fix (subst σ A) (subst (upSub σ) t)
  | ind I => ind I
  | roll I c params recs =>
      roll I c (params.map (subst σ)) (recs.map (subst σ))
  | case I scrut C brs =>
      case I (subst σ scrut) (subst σ C) (brs.map (subst σ))

/-- Substitute `u` for de Bruijn variable `0`. -/
def subst0 (u : Tm) (t : Tm) : Tm :=
  subst (fun
    | 0 => u
    | x + 1 => var x) t

end Tm

end Syntax
end Cyclic
end Scidonia
