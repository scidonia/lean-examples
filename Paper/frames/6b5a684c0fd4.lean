def update (c : CHeap) (handles : List Ref) (r : Ref) (ks : List Ref) : CHeap × List Ref :=
  if CHeap.count c r = 1 then
    (CHeap.cascade (CHeap.writeSlots c r ks), handles)
  else
    ((fresh c ks, cellOf ks) :: CHeap.addOccurrences (CHeap.adjust c r (· - 1)) ks,
      fresh c ks :: dropHandle handles r)
