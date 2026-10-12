theorem bridge_pval (s : Array UInt64) (t : Scidonia.FracPerm.Structured.PTree α) :
    pval s (liftP t) = Scidonia.FracPerm.Structured.pval s t := by
