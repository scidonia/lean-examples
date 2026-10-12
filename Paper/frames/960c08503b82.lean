theorem transport_read_after_replace (d : Desc) (τ : Type) (toEl : τ → El d)
    (ofEl : El d → τ) (ofEl_toEl : ∀ x, ofEl (toEl x) = x)
    (toEl_ofEl : ∀ y, toEl (ofEl y) = y) (s t : τ) :
    (transport d τ toEl ofEl ofEl_toEl toEl_ofEl).observe ()
      ((transport d τ toEl ofEl ofEl_toEl toEl_ofEl).replace t s).1 = t := by
