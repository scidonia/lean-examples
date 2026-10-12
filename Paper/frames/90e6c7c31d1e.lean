theorem universe_read_after_replace (d : Desc) (s : Described d) (x : El d) :
    (describedStateVar d).observe () ((describedStateVar d).replace x s).1 = x := by
