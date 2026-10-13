theorem encodeEl_injective : ∀ (d : Desc) (x y : El d),
    encodeEl d x = encodeEl d y → x = y
