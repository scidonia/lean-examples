def uses : Expr → List Var
  | .var x => [x]
  | .lam x body => (uses body).filter (fun y => y ≠ x)
  | .app f a => uses f ++ uses a
  | .bind x e₁ e₂ => uses e₁ ++ (uses e₂).filter (fun y => y ≠ x)
  | .matchC s _ ys body => uses s ++ (uses body).filter (fun y => y ∉ ys)
  | .dup x e => x :: uses e
  | .drop x e => x :: uses e
  | .con0 _ => []
  | .con1 _ a => uses a
  | .con2 _ a b => uses a ++ uses b
  | .store s _ v => uses s ++ uses v

def Closed (e : Expr) : Prop := uses e = []
