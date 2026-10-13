theorem ofState_toState {σ : Type} [SealedStateVar σ] (s : σ) :
    ofState (toState s) = s :=
