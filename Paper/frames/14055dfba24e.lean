theorem writer_authority_add {c : PConf inst} (hw : WFConf inst c) :
    writerAuthority inst c + readerShare inst c = 1 := by
