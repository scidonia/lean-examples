namespace Scidonia
namespace Cyclic
namespace Syntax
namespace StrictPos

/-- Signature of one constructor: a list of non-recursive parameter types,
plus the number of recursive fields. -/
structure CtorSig (Ty : Type u) where
  paramTys : List Ty
  recArity : Nat

/-- Signature of one inductive: universe level + list of constructors. -/
structure IndSig (Ty : Type u) where
  level : Nat
  ctors : List (CtorSig Ty)

def ctorParamArity {Ty : Type u} (c : CtorSig Ty) : Nat :=
  c.paramTys.length

def lookup {A : Type u} (xs : List A) (n : Nat) : Option A :=
  xs[n]?

def lookupInd {Ty : Type u} (env : List (IndSig Ty)) (I : Nat) : Option (IndSig Ty) :=
  lookup env I

def lookupCtor {Ty : Type u} (sig : IndSig Ty) (c : Nat) : Option (CtorSig Ty) :=
  lookup sig.ctors c

theorem lookupCtor_lt {Ty : Type u} (sig : IndSig Ty) (c : Nat) (ctor : CtorSig Ty) :
    lookupCtor (Ty := Ty) sig c = some ctor → c < sig.ctors.length := by
  intro h
  unfold lookupCtor lookup at h
  sorry

end StrictPos
end Syntax
end Cyclic
end Scidonia
