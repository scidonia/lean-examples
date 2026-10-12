theorem describedLayout_read_after_replace (d : Layout) (p : ObsPath d)
    (x : ObsEl p.obs) (s : DescribedLayout d) (h : (setLeaf p x s.value).2 = true) :
    (describedLayoutStateVar d).observe p
      ((describedLayoutStateVar d).replace ⟨p, x⟩ s).1 = some x := by
