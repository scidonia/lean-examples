inductive Owns (ρ : TEnv) : Multi → Expr → Prop where
  | drop {m : Multi} {y : Var} {r : Ref} {e : Expr} (hρ : ρ.lookup y = some r)
      (hmem : (y, r) ∈ m) : Owns ρ m (.drop y e)
  | bindVar {m : Multi} {x z : Var} {r : Ref} {e₂ : Expr} (hρ : ρ.lookup z = some r)
      (hmem : (z, r) ∈ m) (hheld : ∀ p ∈ m, p.1 = x → p.2 = r) :
      Owns ρ m (.bind x (.var z) e₂)
  | appVar {m : Multi} {x z : Var} {r : Ref} {body : Expr} (hρ : ρ.lookup z = some r)
      (hmem : (z, r) ∈ m) (hheld : ∀ p ∈ m, p.1 = x → p.2 = r) :
      Owns ρ m (.app (.lam x body) (.var z))
  | store {m : Multi} {y : Var} {r : Ref} {i : Nat} {v : Expr} (hρ : ρ.lookup y = some r)
      (hmem : (y, r) ∈ m) : Owns ρ m (.store (.var y) i v)
