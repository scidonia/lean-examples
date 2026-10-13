inductive Root : Expr → Expr → Prop where
  | beta {x : Var} {body v : Expr} : Value v → Root (.app (.lam x body) v) (subst x v body)
  | bindVal {x : Var} {v body : Expr} : Value v → Root (.bind x v body) (subst x v body)
  | matchVal {s : Expr} {c : Ctor} {ys : List Var} {body : Expr} : Value s →
      nodeTag? s = some c → ys.length = (nodeFields s).length →
      Root (.matchC s c ys body) (substAll ys (nodeFields s) body)
  | storeVal {s : Expr} {i : Nat} {v n' : Expr} : Value s → Value v →
      slotUpdate s i v = some n' → Root (.store s i v) n'
