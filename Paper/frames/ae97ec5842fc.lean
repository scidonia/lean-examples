inductive TStep :
    CHeap → List Ref → TEnv → Multi → Expr → CHeap → List Ref → TEnv → Multi → Expr → Prop where
  | dup {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {r : Ref} {e : Expr}
      (hρ : ρ.lookup y = some r) (hlive : r ∈ CHeap.refs c) :
      TStep c hs ρ m (.dup y e) (dup c hs r).1 hs ρ (Multi.insert m y r) e
  | dropShared {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {r : Ref}
      {e : Expr} (hρ : ρ.lookup y = some r) (h2 : 2 ≤ CHeap.count c r)
      (hsub : (y, r) ∈ m) :
      TStep c hs ρ m (.drop y e) (decRef c hs r).1 hs ρ (Multi.dropOcc m y r) e
  | dropFinal {c : CHeap} {hs : List Ref} {ρ : TEnv} {m : Multi} {y : Var} {r : Ref}
      {e : Expr} (hρ : ρ.lookup y = some r) (h1 : CHeap.count c r = 1)
      (hsub : (y, r) ∈ m) :
      TStep c hs ρ m (.drop y e) (release c hs r).1 hs ρ (Multi.dropOcc m y r) e
