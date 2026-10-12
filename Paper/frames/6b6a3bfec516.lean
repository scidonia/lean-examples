theorem universe_read_detached (d : Desc) (ℓ : Loc) (s : Described d) :
    NoRef ℓ (encodeEl d ((describedStateVar d).observe () s)) :=
