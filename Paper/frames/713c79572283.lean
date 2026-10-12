class SealedStateVar (σ : Type) where
  layout : Layout
  rep : σ = State layout
