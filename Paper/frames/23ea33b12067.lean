theorem uses_subst_of_closed : ∀ (e : Expr) (x : Var) (v : Expr), Pure e → Closed v →
    uses (subst x v e) = (uses e).filter (fun y => y ≠ x)
