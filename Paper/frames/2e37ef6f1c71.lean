theorem encodeObs_injective : ∀ (o : ObsDesc) (x y : ObsEl o),
    encodeObs o x = encodeObs o y → x = y
