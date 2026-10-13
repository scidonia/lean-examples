theorem read_frame {d : Layout} (p q : ObsPath d) (s s' : State d) (new : ObsEl p.obs)
    (hdisjoint : Disjoint p.path q.path) (hwrite : setLeaf p new s = (s', true)) :
    read? q s' = read? q s := by
