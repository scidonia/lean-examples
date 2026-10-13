theorem runFresh_eq_pval (init : Scidonia.FracPerm.Structured.Init)
    (p : Scidonia.FracPerm.Structured.Program α) :
    Scidonia.FracPerm.Structured.runFresh init p = (do
      let a : Array UInt64 := LawfulStateVar.initial init
      return pval a (liftP (Scidonia.FracPerm.Structured.Program.treeOf p))) := by
