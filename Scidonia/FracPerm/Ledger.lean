/-
The ghost ledger behind the fractional-permission object interface.

A `Ledger` records the reads currently lent out to the caller as pairs of a
ghost identifier and a fraction. It is pure specification: no `Ledger` value
is ever built at run time, and every proposition about one lives in `Prop`,
so the compiler erases it (see `Scidonia.FracPerm.Hoare`).

The identifier of an entry is ghost state too. It exists only so that a
`ReadTok` can name *which* entry it is entitled to return: the fraction `q`
alone would not distinguish two outstanding reads of the same size.
-/
namespace Scidonia.FracPerm

/-- The outstanding reads: `(ghost id, fraction)` for each read taken out. -/
abbrev Ledger := List (Nat × Rat)

namespace Ledger

/-- The fraction of the array the caller still holds: the whole minus what is
lent out. The empty ledger holds everything, so writes are allowed there. -/
def held (l : Ledger) : Rat := 1 - (l.map Prod.snd).sum

/-- Nothing is lent out, so the caller holds the whole array. -/
theorem held_nil : held [] = 1 := by simp [held]; grind

/-- Renting out the fraction `q` lowers the held fraction by exactly `q`. -/
theorem held_cons (n : Nat) (q : Rat) (l : Ledger) : held ((n, q) :: l) = held l - q := by
  simp [held]; grind

/-- Returning the fraction `q` recorded by an entry the ledger holds raises the
held fraction by exactly `q`. This is the whole point of the interface: a
returned read gives back exactly what it took, no more and no less. -/
theorem held_erase_of_mem {n : Nat} {q : Rat} {l : Ledger} (h : (n, q) ∈ l) :
    held (l.erase (n, q)) = held l + q := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    obtain ⟨n', q'⟩ := x
    rcases List.mem_cons.mp h with h | h
    · cases h
      rw [List.erase_cons_head, held_cons]
      grind
    · by_cases hx : (n', q') = (n, q)
      · rw [hx, List.erase_cons_head, held_cons]
        grind
      · have hxb : ¬((n', q') == (n, q)) = true := by simpa [beq_iff_eq] using hx
        rw [List.erase_cons_tail hxb, held_cons, held_cons, ih h]
        grind

end Ledger

end Scidonia.FracPerm
