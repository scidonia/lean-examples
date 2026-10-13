@[instance_reducible]
def transport (d : Desc) (τ : Type) (toEl : τ → El d) (ofEl : El d → τ)
    (ofEl_toEl : ∀ x, ofEl (toEl x) = x) (toEl_ofEl : ∀ y, toEl (ofEl y) = y) :
    LawfulStateVar τ τ Unit τ where
  Result _ := τ
  initial s := ofEl (toEl s)
  Valid _ := True
  observe _ s := ofEl (toEl s)
  replace x s := (ofEl (toEl x), true)
  encodeRead _ s := encodeEl d (toEl s)
  initial_valid _ := trivial
  replace_valid _ _ _ := trivial
  encodeRead_injective _ x y h := by
    have h' : toEl x = toEl y := encodeEl_injective d (toEl x) (toEl y) h
    calc x = ofEl (toEl x) := (ofEl_toEl x).symm
      _ = ofEl (toEl y) := by rw [h']
      _ = y := ofEl_toEl y
  observe_detached ℓ _ s _ := by
    show NoRef ℓ (encodeEl d (toEl (ofEl (toEl s))))
    rw [toEl_ofEl]
    exact encodeEl_noRef ℓ d (toEl s)
