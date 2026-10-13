def Heap.update (h : Heap σ) (ℓ : Loc) (v : Option σ) : Heap σ :=
  fun m => if m = ℓ then v else h m

theorem Heap.update_self (h : Heap σ) (ℓ : Loc) (v : Option σ) :
    Heap.update h ℓ v ℓ = v := by
  unfold Heap.update
  simp

theorem Heap.update_of_ne {h : Heap σ} {ℓ m : Loc} (hm : m ≠ ℓ) (v : Option σ) :
    Heap.update h ℓ v m = h m := by
  unfold Heap.update
  simp [hm]
