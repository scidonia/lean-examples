theorem not_noRef_loc_self (ℓ : Loc) : ¬ NoRef ℓ (.loc ℓ) := fun h => h rfl
