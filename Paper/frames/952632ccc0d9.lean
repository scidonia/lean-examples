inductive Desc where
  | unit
  | nat
  | sum (left right : Desc)
deriving DecidableEq, Repr

abbrev El : Desc → Type
  | .unit => Unit
  | .nat => Nat
  | .sum left right => Sum (El left) (El right)

def slotDesc : Desc := .sum .unit .nat
