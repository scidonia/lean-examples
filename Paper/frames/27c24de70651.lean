abbrev sealedWords : Layout5.Layout := .arr (.leaf .uint)

instance : SealedStateVar (Array UInt64) := ⟨sealedWords, rfl⟩
