def runBenchmark (seed : Nat) : IO Unit := do
  IO.println "bench: the array update, exclusive (the caller alone refers to the array) against aliased (a live second reference)"
  for n in benchSizes do
    reportArrayBench (← benchArrayRow n seed)
  IO.println "bench: the tree update, exclusive against aliased; the walk is in both columns, so the extra is the allocation of the cells the update rebuilt"
  for k in benchDepths do
    reportTreeBench (← benchTreeRow k seed.toUInt64)
  IO.println "bench: per-operation times are means over arrayOps (treeOps) updates and arrayReps (treeReps) measurements; a measurement of this program on this toolchain, not a complexity theorem"
