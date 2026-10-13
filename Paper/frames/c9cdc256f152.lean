inductive RTree : Type → Type 1 where
  | pure {α : Type} (a : α) : RTree α
  | get {α : Type} (i : Nat) (k : Option UInt64 → RTree α) : RTree α
  | size {α : Type} (k : Nat → RTree α) : RTree α
  | fork {α β γ : Type} (l : RTree β) (r : RTree γ)
      (k : β × γ → RTree α) : RTree α

inductive PTree : Type → Type 1 where
  | pure {α : Type} (a : α) : PTree α
  | set {α : Type} (i : Nat) (v : UInt64) (k : Bool → PTree α) : PTree α
  | phase {α β : Type} (r : RTree β) (k : β → PTree α) : PTree α
