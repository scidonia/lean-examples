private inductive Context : (d : Layout) → Path d → Type where
  | here (d : Layout) : Context d .here
  | left {a b : Layout} {p : Path a} (inner : Context a p) (right : State b) :
      Context (.struct a b) (.left p)
  | right {a b : Layout} {p : Path b} (left : State a) (inner : Context b p) :
      Context (.struct a b) (.right p)
  | index {a : Layout} {p : Path a} (i : Nat) (siblings : Array (State a))
      (bound : i < siblings.size) (inner : Context a p) : Context (.arr a) (.index i p)
