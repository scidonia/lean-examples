theorem setLeaf_failed {d : Layout} (p : ObsPath d) (x : ObsEl p.obs) (s : State d)
    (h : (setLeaf p x s).2 = false) : (setLeaf p x s).1 = s := by
