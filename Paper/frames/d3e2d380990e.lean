inductive Slot where
  | empty
  | full (value : Nat)
deriving DecidableEq, Repr

def encode : Slot → El slotDesc
  | .empty => Sum.inl ()
  | .full n => Sum.inr n

def decode : El slotDesc → Slot
  | Sum.inl _ => .empty
  | Sum.inr n => .full n
