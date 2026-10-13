theorem describedLayout_primitive_detached (d : Layout) (ℓ : Loc) (p : ObsPath d)
    (s : DescribedLayout d) :
    NoRef ℓ ((describedLayoutStateVar d).encodeRead p
      ((describedLayoutStateVar d).observe p s)) :=
