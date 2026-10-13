structure Reader (α : Type) where
  private mk ::
  private tree : RTree α

structure Program (α : Type) where
  private mk ::
  private tree : PTree α
