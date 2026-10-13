theorem encodeEl_noRef (ℓ : Loc) : ∀ (d : Desc) (x : El d), NoRef ℓ (encodeEl d x)
