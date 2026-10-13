inductive RTree (ReadOp : Type) (Result : ReadOp → Type) : Type → Type 1 where
  | pure {α : Type} (a : α) : RTree ReadOp Result α
  | read {α : Type} (o : ReadOp) (k : Result o → RTree ReadOp Result α) :
      RTree ReadOp Result α
  | fork {α β γ : Type} (l : RTree ReadOp Result β) (r : RTree ReadOp Result γ)
      (k : β × γ → RTree ReadOp Result α) : RTree ReadOp Result α

inductive PTree (ReadOp : Type) (Result : ReadOp → Type) (WriteOp : Type) :
    Type → Type 1 where
  | pure {α : Type} (a : α) : PTree ReadOp Result WriteOp α
  | write {α : Type} (w : WriteOp) (k : Bool → PTree ReadOp Result WriteOp α) :
      PTree ReadOp Result WriteOp α
  | phase {α β : Type} (r : RTree ReadOp Result β)
      (k : β → PTree ReadOp Result WriteOp α) : PTree ReadOp Result WriteOp α
