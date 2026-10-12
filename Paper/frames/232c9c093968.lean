theorem toState_ofState {σ : Type} [SealedStateVar σ]
    (t : State (SealedStateVar.layout (σ := σ))) : toState (ofState (σ := σ) t) = t :=
