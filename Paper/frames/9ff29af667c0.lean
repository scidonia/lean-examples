theorem writer_authority_add {c : PConf} (hw : WFConf c) :
    writerAuthority c + readerShare c = 1 := by
