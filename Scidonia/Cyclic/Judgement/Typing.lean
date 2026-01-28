import Scidonia.Cyclic.Syntax.Term
import Scidonia.Cyclic.Syntax.StrictPos

namespace Scidonia
namespace Cyclic
namespace Judgement

open Scidonia.Cyclic.Syntax

namespace Typing

abbrev Ctx : Type := List Syntax.Tm
abbrev Env : Type := List (Syntax.StrictPos.IndSig Syntax.Tm)

/-- Telescope contexts with shift-aware lookup (Coq's `ctx_lookup`). -/
def ctxLookup : Ctx → Nat → Option Syntax.Tm
  | [], _ => none
  | A :: _, 0 => some (Syntax.Tm.shift 1 0 A)
  | _ :: Γ, Nat.succ x => (ctxLookup Γ x).map (Syntax.Tm.shift 1 0)

def ctxExtend (Γ : Ctx) (A : Syntax.Tm) : Ctx := A :: Γ

/-- Build nested Π-types from a list of domains.

Because `Tm.pi` binds one variable in its body (de Bruijn), we shift
both domain types and the codomain as we descend under binders.
-/
def mkPisAux (k : Nat) : List Syntax.Tm → Syntax.Tm → Syntax.Tm
  | [], B => Syntax.Tm.shift k 0 B
  | A :: As, B =>
      Syntax.Tm.pi (Syntax.Tm.shift k 0 A) (mkPisAux (k + 1) As B)

def mkPis (As : List Syntax.Tm) (B : Syntax.Tm) : Syntax.Tm :=
  mkPisAux 0 As B

inductive HasType (env : Env) : Ctx → Syntax.Tm → Syntax.Tm → Prop
  | ty_var (Γ : Ctx) (x : Nat) (A : Syntax.Tm) :
      ctxLookup Γ x = some A →
      HasType env Γ (Syntax.Tm.var x) A

  | ty_sort (Γ : Ctx) (i : Nat) :
      HasType env Γ (Syntax.Tm.sort i) (Syntax.Tm.sort (Nat.succ i))

  | ty_pi (Γ : Ctx) (A B : Syntax.Tm) (i j : Nat) :
      HasType env Γ A (Syntax.Tm.sort i) →
      HasType env (ctxExtend Γ A) B (Syntax.Tm.sort j) →
      HasType env Γ (Syntax.Tm.pi A B) (Syntax.Tm.sort (Nat.max i j))

  | ty_lam (Γ : Ctx) (A t B : Syntax.Tm) (i : Nat) :
      HasType env Γ A (Syntax.Tm.sort i) →
      HasType env (ctxExtend Γ A) t B →
      HasType env Γ (Syntax.Tm.lam A t) (Syntax.Tm.pi A B)

  | ty_app (Γ : Ctx) (t u A B : Syntax.Tm) :
      HasType env Γ t (Syntax.Tm.pi A B) →
      HasType env Γ u A →
      HasType env Γ (Syntax.Tm.app t u) (Syntax.Tm.subst0 u B)

  | ty_fix (Γ : Ctx) (A t : Syntax.Tm) (i : Nat) :
      HasType env Γ A (Syntax.Tm.sort i) →
      HasType env (ctxExtend Γ A) t (Syntax.Tm.shift 1 0 A) →
      HasType env Γ (Syntax.Tm.fix A t) A

  | ty_ind (Γ : Ctx) (I : Nat) (sigI : Syntax.StrictPos.IndSig Syntax.Tm) :
      Syntax.StrictPos.lookupInd env I = some sigI →
      HasType env Γ (Syntax.Tm.ind I) (Syntax.Tm.sort (Nat.succ sigI.level))

  | ty_roll (Γ : Ctx) (I : Nat) (sigI : Syntax.StrictPos.IndSig Syntax.Tm)
      (c : Nat) (ctor : Syntax.StrictPos.CtorSig Syntax.Tm)
      (params recs : List Syntax.Tm) :
      Syntax.StrictPos.lookupInd env I = some sigI →
      Syntax.StrictPos.lookupCtor sigI c = some ctor →
      params.length = ctor.paramTys.length →
      (∀ (n : Nat) (t A : Syntax.Tm),
        params[n]? = some t →
        ctor.paramTys[n]? = some A →
        HasType env Γ t A) →
      (∀ (n : Nat) (r : Syntax.Tm),
        recs[n]? = some r →
        HasType env Γ r (Syntax.Tm.ind I)) →
      recs.length = ctor.recArity →
      HasType env Γ (Syntax.Tm.roll I c params recs) (Syntax.Tm.ind I)

  | ty_case (Γ : Ctx) (I : Nat) (sigI : Syntax.StrictPos.IndSig Syntax.Tm)
      (scrut C : Syntax.Tm) (brs : List Syntax.Tm) (i : Nat) :
      Syntax.StrictPos.lookupInd env I = some sigI →
      brs.length = sigI.ctors.length →
      HasType env Γ scrut (Syntax.Tm.ind I) →
      HasType env Γ C (Syntax.Tm.sort i) →
      (∀ (c : Nat) (ctor : Syntax.StrictPos.CtorSig Syntax.Tm),
        Syntax.StrictPos.lookupCtor sigI c = some ctor →
        c < brs.length) →
      (∀ (c : Nat) (ctor : Syntax.StrictPos.CtorSig Syntax.Tm) (br : Syntax.Tm),
        Syntax.StrictPos.lookupCtor sigI c = some ctor →
        Syntax.Tm.branch brs c = some br →
        HasType env Γ br
          (mkPis (ctor.paramTys ++ List.replicate ctor.recArity (Syntax.Tm.ind I)) C)) →
      HasType env Γ (Syntax.Tm.case I scrut C brs) C

end Typing

end Judgement
end Cyclic
end Scidonia
