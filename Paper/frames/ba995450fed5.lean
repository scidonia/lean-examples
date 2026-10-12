theorem pstep_wf {c c' : PConf inst} (h : PStep inst c c') (hw : WFConf inst c) :
    WFConf inst c' := by
