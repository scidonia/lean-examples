structure Counter where
  hits : Nat
  log : Array Nat

namespace Counter

inductive ReadOp where
  | hits
  | entry (i : Nat)

def Result : ReadOp → Type
  | .hits => Nat
  | .entry _ => Option Nat

inductive WriteOp where
  | bump
  | record (x : Nat)
