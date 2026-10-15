def RuntimeAgrees (h : Presentation) (handles : List Ref) (r : Ref) (rc : Int32) : Prop :=
  Exclusive h handles r → RefCount.IsExclusive rc
