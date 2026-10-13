inductive Lower : Occs → Occs → Expr → Expr → Prop where
  | var {Δ Γ x} (h : x ∈ Γ ∨ x ∈ Δ) : Lower Δ Γ (.var x) (wrap Γ [x] (.var x))
  | lam {Δ Γ x body body'} (h : Lower (forget Δ x) (bindEnv Γ x (uses body)) body body') :
      Lower Δ Γ (.lam x body) (wrap Γ (uses (.lam x body)) (.lam x body'))
  | app {Δ Γ f a f' a'} (hf : Lower Δ (claimEnv Γ (uses f)) f f')
      (ha : Lower Δ (claimEnv Γ (uses a)) a a') :
      Lower Δ Γ (.app f a) (wrap Γ (uses (.app f a)) (.app f' a'))
  | bind {Δ Γ x e₁ e₂ e₁' e₂'} (h₁ : Lower Δ (claimEnv Γ (uses e₁)) e₁ e₁')
      (h₂ : Lower (forget Δ x) (bindEnv Γ x (uses e₂)) e₂ e₂') :
      Lower Δ Γ (.bind x e₁ e₂) (wrap Γ (uses (.bind x e₁ e₂)) (.bind x e₁' e₂'))
  | matchC {Δ Γ s c ys body s' body'} (hs : Lower Δ (claimEnv Γ (uses s)) s s')
      (h : Lower (forgetAll Δ ys) (armEnv Γ ys (uses body)) body body') :
      Lower Δ Γ (.matchC s c ys body)
        (wrap Γ (uses (.matchC s c ys body)) (.matchC s' c ys body'))
  | con0 {Δ Γ c} : Lower Δ Γ (.con0 c) (wrap Γ [] (.con0 c))
  | con1 {Δ Γ c a a'} (h : Lower Δ (claimEnv Γ (uses a)) a a') :
      Lower Δ Γ (.con1 c a) (wrap Γ (uses (.con1 c a)) (.con1 c a'))
  | con2 {Δ Γ c a b a' b'} (h₁ : Lower Δ (claimEnv Γ (uses a)) a a')
      (h₂ : Lower Δ (claimEnv Γ (uses b)) b b') :
      Lower Δ Γ (.con2 c a b) (wrap Γ (uses (.con2 c a b)) (.con2 c a' b'))
  | store {Δ Γ s i v s' v'} (hs : Lower Δ (claimEnv Γ (uses s)) s s')
      (h : Lower Δ (claimEnv Γ (uses v)) v v') :
      Lower Δ Γ (.store s i v) (wrap Γ (uses (.store s i v)) (.store s' i v'))
