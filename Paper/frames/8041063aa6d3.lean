theorem bridge_val (s : Array UInt64) (t : Scidonia.FracPerm.Structured.RTree α) :
    val s (liftR t) = Scidonia.FracPerm.Structured.val s t := by
