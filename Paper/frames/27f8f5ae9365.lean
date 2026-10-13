def CHeap.WF (c : CHeap) : Prop := (CHeap.refs c).Nodup

def CHeap.Live (c : CHeap) : Prop := c.find? (fun e => e.2.count == 0) = none
