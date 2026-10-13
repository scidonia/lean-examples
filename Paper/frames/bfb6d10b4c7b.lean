inductive Value where
  | loc (address : Loc)
  | unit
  | nat (n : Nat)
  | uint (n : UInt64)
  | bool (b : Bool)
  | none
  | some (v : Value)
  | inl (v : Value)
  | inr (v : Value)
  | pair (l r : Value)
deriving Repr, DecidableEq
