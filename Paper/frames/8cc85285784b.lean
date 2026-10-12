def acquire (n : Nat) (q : Rat) :
    HSt σ (fun l _ => n ∉ l.map Prod.fst ∧ 0 < q ∧ q ≤ l.held) (ReadTok n q)
      (fun l s _ l' s' => l' = (n, q) :: l ∧ s' = s) :=
  ⟨fun _ s _ => ⟨(⟨⟩, s), fun _ _ => ⟨_, rfl, rfl⟩⟩⟩

def read [FracObject σ ReadOp WriteOp] {n : Nat} {q : Rat} (_t : ReadTok n q) (o : ReadOp) :
    HSt σ (fun l _ => (n, q) ∈ l) (FracObject.Result (σ := σ) o)
      (fun l s v l' s' => l' = l ∧ s' = s ∧ v = FracObject.observe o s) :=
  ⟨fun _ s _ => ⟨(FracObject.observe o s, s), fun l _ => ⟨l, rfl, rfl, rfl⟩⟩⟩

def release {n : Nat} {q : Rat} (_t : ReadTok n q) :
    HSt σ (fun l _ => (n, q) ∈ l) Unit
      (fun l s _ l' s' => l' = l.erase (n, q) ∧ s' = s) :=
  ⟨fun _ s _ => ⟨((), s), fun _ _ => ⟨_, rfl, rfl⟩⟩⟩

def write [FracObject σ ReadOp WriteOp] (o : WriteOp) :
    HSt σ (fun l _ => l.held = 1) Unit
      (fun l s _ l' s' => l' = l ∧ s' = FracObject.update o s) :=
  ⟨fun _ s _ =>
      ⟨((), FracObject.update o (FracObject.check "Scidonia.FracPerm.HSt.write" o s)),
        fun l _ => ⟨l, rfl,
          congrArg (FracObject.update o) (FracObject.check_eq _ o s)⟩⟩⟩
