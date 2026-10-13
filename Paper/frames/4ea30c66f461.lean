theorem primitive_detached {s : σ} (hs : inst.Valid s) :
    NoRef ℓ (inst.encodeRead o (inst.observe o s)) :=
