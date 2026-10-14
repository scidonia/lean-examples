/-
The per-node fractional account of a tree state, its laws, and the sibling and
fork witnesses.

**The account.** A layout's state is a tree, and a *node* of it is a logical
in-bounds `Path`. `Account d` records, for each node, the reads currently lent
out there as the existing `Scidonia.FracPerm.Ledger` — pairs of a ghost
identifier and a fraction. The identifier is what distinguishes two outstanding
reads of the same size, so a node's account is not merely a sum of fractions;
`heldAt` is the fraction of the node the owner still holds, and it is the
existing `Ledger.held`.

**Per-node local accounting.** Every law here is about *one* node. A descent
keeps the ancestor's allocated share on its spine and obtains a separate positive
share at the child from the child's own account; nothing asserts
`q_child = q_parent / 2`, which would make a fraction-1 write under a fractional
ancestor impossible. Only concurrent holders of the *same* node split, and they
split by halving: `lend` takes a loan out of what an owner holds and `repay` puts
it back (`heldAt_lend`, `heldAt_repay`); `fork` halves one holder's share between
two holders of that node and leaves the node's own fraction exactly where it was
(`heldAt_fork`), and `join` puts the halves back (`heldAt_join`). The halving is
the existing `ValidShare`/`half_valid`/`halves_rejoin` arithmetic.

**The account's authority is proof-side, and reaches no executable.** `Account d`
is `Type`-level data — a finite association list from paths to the existing
`Ledger` — and it is proof-side only: it is never a parameter or a result of the
evaluation. `evalTree` is a function of the layout, the state and the term, and
the private interpreter `runTree` of those and the session's own handle function
and environment; neither names an account, so a caller reaches the executable
with no authority in hand. The `IO` runner's account is only the index of the
judgement it is handed, which is a `Prop` argument rather than a run-time value.
The guarantee is that **no authority representation reaches the executable**.

**The account's conditions are propositions.** `ValidAccount` requires every lent
share to be a positive fraction of at most the whole, the shares at one node to
fit in it, a node's ledger to name each loan at most once, and no node to be
listed twice; `lend`, `repay`, `fork` and `join` each preserve it (`lend_valid`,
`repay_valid`, `fork_valid`, `join_valid`). `ValidAccount` itself, `HandleWF`,
`WriteHolds` and the borrow scope `ReadLoan` are `Prop`s. The borrow scope of a
read names its identifier, its leaf and the share it holds at each node of that
leaf's path, so nothing about a borrow is data a caller could inspect.

**What is proved.** A node whose account is empty is held whole
(`writes_holds_one`), and no other holder fits beside it (`cannot_add_reader`,
`writer_excludes_reader`, `spine_writer_excludes`); two *distinct* holders of one
node fit in the whole (`share_fit`) and a holder's share never exceeds it
(`share_le_one`, `node_shares_positive`); a loan and its return move the held
fraction by exactly the loan (`heldAt_lend`, `heldAt_repay`) and a returned loan
cannot be returned twice (`repay_not_mem`); a read holds a positive share at
every node of its path and fits beside any other holder of those nodes
(`spine_readThrough_positive`, `readThrough_fits`); and `spine_sibling_compatible`
exhibits the witness the milestone rests on — a reader owning half of the common
root and half of the left leaf, a writer holding the root's other half and the
whole right subtree, the root summing to one and the right subtree excluding
every other holder. `multiAccount_valid` is the three-holder witness: one node
whose holders are a half, a quarter and a quarter, reached by a loan, a fork and
a second loan, valid at every step and with the node's own fraction conserved at
every step.
-/
import Scidonia.FracPerm.Ledger
import Scidonia.FracPerm.StateVar.Heap
import Scidonia.FracPerm.StateVar.Layout5

namespace Scidonia.RC

namespace TreeOwnership

open Scidonia.FracPerm (Ledger)
open Scidonia.FracPerm.StateVar (ValidShare half_valid halves_rejoin cannot_add_reader)
open Scidonia.FracPerm.StateVar.Layout5

/-! ## The account -/

/-- A per-node account: for each node of the layout, the reads lent out there.
A node the account does not mention has lent out nothing, and the account is a
finite association list rather than a function, so a validity claim about one is
a finite conjunction.

The account is `Type`-level proof-side data, and the guarantee it is held to is
that **no authority representation reaches the executable**: it is never a
parameter or a result of the evaluation. `evalTree` is handed the layout, the
state and the term, and `runTree` those and the session's own handle function and
environment; the runner's account is only the index of the judgement it is
handed. The account's own conditions `ValidAccount`, `HandleWF`, `WriteHolds` and
`ReadLoan` are `Prop`s. -/
abbrev Account (d : Layout) := List (Path d × Ledger)

/-- The ledger at a node: the account's first entry for it, or the empty ledger
when the account holds none. -/
def ledgerAt {d : Layout} : Account d → Path d → Ledger
  | [], _ => []
  | (q, l) :: rest, p => if p = q then l else ledgerAt rest p

/-- The fraction of a node its owner still holds: the whole minus what is lent
out there. -/
abbrev heldAt {d : Layout} (A : Account d) (p : Path d) : Rat :=
  Scidonia.FracPerm.Ledger.held (ledgerAt A p)

/-- A read is outstanding at a node: the ghost identifier and the fraction it
holds there. -/
abbrev Reads {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat) : Prop :=
  (i, q) ∈ ledgerAt A p

/-- The holder of a node holds it whole: nothing is lent out there. -/
abbrev Writes {d : Layout} (A : Account d) (p : Path d) : Prop := ledgerAt A p = []

/-- An account is valid when every lent share is a positive fraction of at most
the whole, the shares at one node fit in the whole, a node's ledger names each
loan at most once, and no node appears twice. -/
def ValidAccount {d : Layout} (A : Account d) : Prop :=
  (∀ e ∈ A, (∀ x ∈ e.2, ValidShare x.2) ∧ (e.2.map Prod.snd).sum ≤ 1 ∧ e.2.Nodup)
    ∧ (A.map Prod.fst).Nodup

/-- The entry an account prepends is the entry its node reads back. -/
theorem ledgerAt_cons_self {d : Layout} (A : Account d) (p : Path d) (l : Ledger) :
    ledgerAt ((p, l) :: A) p = l := by
  simp [ledgerAt]

/-- An account that holds nothing at a node holds that node whole. -/
theorem heldAt_empty {d : Layout} (A : Account d) {p : Path d} (h : ledgerAt A p = []) :
    heldAt A p = 1 := by
  rw [heldAt, h, Scidonia.FracPerm.Ledger.held_nil]

/-- A node whose account is empty is held whole. -/
theorem writes_holds_one {d : Layout} {A : Account d} {p : Path d} (h : Writes A p) :
    heldAt A p = 1 :=
  heldAt_empty A h

/-- Two distinct loans at one node are distinct entries, so a holder's node is
the identifier as well as the fraction. -/
theorem reads_self {d : Layout} {A : Account d} {p : Path d} {i : Nat} {q : Rat}
    (h : Reads A p i q) : ∃ l, ledgerAt A p = l ∧ (i, q) ∈ l := ⟨_, rfl, h⟩

/-- The ledger a valid account holds at a node satisfies the account's own
conditions: the entry is the account's if it has one there, and the empty ledger
does so trivially. -/
theorem ledgerAt_valid {d : Layout} (A : Account d) (p : Path d) : ValidAccount A →
    (∀ x ∈ ledgerAt A p, ValidShare x.2)
      ∧ ((ledgerAt A p).map Prod.snd).sum ≤ 1 ∧ (ledgerAt A p).Nodup := by
  induction A with
  | nil =>
      intro _
      exact ⟨by intro x hx; simp [ledgerAt] at hx, by rw [ledgerAt]; grind, by rw [ledgerAt]; simp⟩
  | cons e es ih =>
      intro hA
      obtain ⟨k, l⟩ := e
      obtain ⟨hval, hkeys⟩ := hA
      rw [List.forall_mem_cons] at hval
      rw [List.map_cons, List.nodup_cons] at hkeys
      by_cases hk : p = k
      · have hlook : ledgerAt ((k, l) :: es) p = l := by simp [ledgerAt, hk]
        rw [hlook]
        exact hval.1
      · have hlook : ledgerAt ((k, l) :: es) p = ledgerAt es p := by simp [ledgerAt, hk]
        rw [hlook]
        exact ih ⟨hval.2, hkeys.2⟩

/-! ## Updating one node's ledger

The account is one entry per node, and every operation below rewrites the node's
own entry in place rather than shadowing it, so a node keeps a single entry and
the account's own well-formedness is preserved. -/

/-- The account with a node's ledger updated: the node's entry becomes `f` of
what it was, and a node the account does not mention gains the entry `f []`. -/
def updateLedger {d : Layout} (A : Account d) (p : Path d) (f : Ledger → Ledger) :
    Account d :=
  match A with
  | [] => [(p, f [])]
  | (q, l) :: rest => if p = q then (q, f l) :: rest else (q, l) :: updateLedger rest p f

/-- Updating a node's ledger reads back exactly the update at that node. -/
theorem ledgerAt_updateLedger_self {d : Layout} (A : Account d) (p : Path d)
    (f : Ledger → Ledger) : ledgerAt (updateLedger A p f) p = f (ledgerAt A p) := by
  induction A with
  | nil => simp [updateLedger, ledgerAt]
  | cons e rest ih =>
      obtain ⟨q, l⟩ := e
      rw [updateLedger]
      split
      · rename_i hpq
        simp [ledgerAt, hpq]
      · rename_i hpq
        simp only [ledgerAt, hpq, reduceIte]
        exact ih

/-- Updating one node's ledger leaves every other node's ledger as it was. -/
theorem ledgerAt_updateLedger_ne {d : Layout} (A : Account d) (p p' : Path d)
    (f : Ledger → Ledger) (h : p' ≠ p) :
    ledgerAt (updateLedger A p f) p' = ledgerAt A p' := by
  induction A with
  | nil => simp [updateLedger, ledgerAt, h]
  | cons e rest ih =>
      obtain ⟨q, l⟩ := e
      rw [updateLedger]
      split
      · rename_i hpq
        have hp'q : ¬ p' = q := fun h' => h (h'.trans hpq.symm)
        simp only [ledgerAt, hp'q, reduceIte]
      · rename_i hpq
        by_cases hp'q : p' = q
        · simp only [ledgerAt, hp'q, reduceIte]
        · simp only [ledgerAt, hp'q, reduceIte]
          exact ih

/-- An entry of an updated account is the node's new entry or an entry the
account already had. -/
theorem mem_updateLedger {d : Layout} (A : Account d) (p : Path d) (f : Ledger → Ledger)
    {e : Path d × Ledger} (h : e ∈ updateLedger A p f) :
    e = (p, f (ledgerAt A p)) ∨ e ∈ A := by
  induction A with
  | nil => exact Or.inl (by simpa [updateLedger, ledgerAt] using h)
  | cons e' rest ih =>
      obtain ⟨q, l⟩ := e'
      rw [updateLedger] at h
      split at h
      · rename_i hpq
        rw [List.mem_cons] at h
        rcases h with h | h
        · refine Or.inl ?_
          rw [h, hpq, ledgerAt_cons_self]
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rename_i hpq
        rw [List.mem_cons] at h
        rcases h with h | h
        · exact Or.inr (by simp [h])
        · rcases ih h with h' | h'
          · refine Or.inl ?_
            rw [h']
            have hlook : ledgerAt ((q, l) :: rest) p = ledgerAt rest p := by
              simp only [ledgerAt, hpq, reduceIte]
            rw [hlook]
          · exact Or.inr (by simp [h'])

/-- A node of an updated account is a node of the account or the updated node. -/
theorem updateLedger_paths {d : Layout} (A : Account d) (p : Path d) (f : Ledger → Ledger)
    {e : Path d × Ledger} (h : e ∈ updateLedger A p f) :
    e.1 ∈ A.map Prod.fst ∨ e.1 = p := by
  induction A with
  | nil =>
      have h1 : e = (p, f []) := by simpa [updateLedger] using h
      exact Or.inr (by rw [h1])
  | cons e' rest ih =>
      obtain ⟨q, l⟩ := e'
      rw [updateLedger] at h
      split at h
      · rename_i hpq
        rw [List.mem_cons] at h
        rcases h with h | h
        · left
          rw [h]
          simp
        · left
          exact List.mem_map.mpr ⟨e, List.mem_cons_of_mem _ h, rfl⟩
      · rename_i hpq
        rw [List.mem_cons] at h
        rcases h with h | h
        · left
          rw [h]
          simp
        · rcases ih h with h' | h'
          · left
            rw [List.mem_map] at h' ⊢
            obtain ⟨z, hz, hz'⟩ := h'
            exact ⟨z, List.mem_cons_of_mem _ hz, hz'⟩
          · right
            exact h'

/-- Updating a node's ledger keeps the account's nodes distinct. -/
theorem updateLedger_nodup {d : Layout} (A : Account d) (p : Path d) (f : Ledger → Ledger)
    (h : (A.map Prod.fst).Nodup) : ((updateLedger A p f).map Prod.fst).Nodup := by
  induction A with
  | nil => simp [updateLedger]
  | cons e' rest ih =>
      obtain ⟨q, l⟩ := e'
      rw [List.map_cons, List.nodup_cons] at h
      rw [updateLedger]
      split
      · simp only [List.map_cons, List.nodup_cons]
        exact ⟨h.1, h.2⟩
      · rename_i hpq
        simp only [List.map_cons, List.nodup_cons]
        have hrest := ih h.2
        refine ⟨?_, hrest⟩
        intro hmem
        rw [List.mem_map] at hmem
        obtain ⟨e, he, hef⟩ := hmem
        rcases updateLedger_paths rest p f he with h' | h'
        · exact h.1 (hef ▸ h')
        · exact hpq (h'.symm.trans hef)

/-- Updating one node's ledger in a way the node's own loans allow keeps the
account valid: every other node's entry is the account's own, and the updated
entry is the caller's. -/
theorem updateLedger_valid {d : Layout} (A : Account d) (p : Path d) (f : Ledger → Ledger)
    (hA : ValidAccount A)
    (hf : (∀ x ∈ f (ledgerAt A p), ValidShare x.2)
      ∧ (f (ledgerAt A p)).Nodup ∧ (f (ledgerAt A p) |>.map Prod.snd).sum ≤ 1) :
    ValidAccount (updateLedger A p f) := by
  refine ⟨?_, updateLedger_nodup A p f hA.2⟩
  intro e he
  rcases mem_updateLedger A p f he with rfl | he
  · exact ⟨hf.1, hf.2.2, hf.2.1⟩
  · exact hA.1 e he

/-- An entry of a ledger that is not the entry erased survives the erasure. -/
theorem mem_erase_of_ne {l : Ledger} {a b : Nat × Rat} (hb : b ∈ l) (h : b ≠ a) :
    b ∈ l.erase a := by
  induction l with
  | nil => simp at hb
  | cons x xs ih =>
      by_cases hxa : x = a
      · rw [hxa, List.erase_cons_head]
        rcases List.mem_cons.mp hb with hb | hb
        · exact absurd (hb.trans hxa) h
        · exact hb
      · rw [List.erase_cons_tail (by simpa [beq_iff_eq] using hxa)]
        rcases List.mem_cons.mp hb with hb | hb
        · exact List.mem_cons.mpr (Or.inl hb)
        · exact List.mem_cons.mpr (Or.inr (ih hb))

/-! ## The loans -/

/-- Lend the fraction `q` at a node under the ghost identifier `i`. -/
def lend {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat) : Account d :=
  updateLedger A p (fun l => l ++ [(i, q)])

/-- Return the loan the identifier `i` holds at a node: the entry is erased, and
a loan the node does not hold leaves the ledger as it was. -/
def repay {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat) : Account d :=
  updateLedger A p (fun l => l.erase (i, q))

/-- Fork the loan `(i, q)` at a node into the two halves `(i, q / 2)` and
`(j, q / 2)`: one holder of the node becomes two, each holding half of what the
one held there. -/
def fork {d : Layout} (A : Account d) (p : Path d) (i j : Nat) (q : Rat) : Account d :=
  updateLedger A p (fun l => l.erase (i, q) ++ [(i, q / 2), (j, q / 2)])

/-- Join the two halves `(i, q / 2)` and `(j, q / 2)` at a node back into the one
loan `(i, q)`: two holders of the node become one, holding between them what the
two held. -/
def join {d : Layout} (A : Account d) (p : Path d) (i j : Nat) (q : Rat) : Account d :=
  updateLedger A p (fun l => (l.erase (i, q / 2)).erase (j, q / 2) ++ [(i, q)])

/-- Lending a fraction appends one entry to the node's ledger. -/
theorem ledgerAt_lend {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat) :
    ledgerAt (lend A p i q) p = ledgerAt A p ++ [(i, q)] := by
  rw [lend, ledgerAt_updateLedger_self]

/-- Returning a loan erases its entry from the node's ledger. -/
theorem ledgerAt_repay {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat) :
    ledgerAt (repay A p i q) p = (ledgerAt A p).erase (i, q) := by
  rw [repay, ledgerAt_updateLedger_self]

/-- Forking a loan replaces its entry at the node by the two halves. -/
theorem ledgerAt_fork {d : Layout} (A : Account d) (p : Path d) (i j : Nat) (q : Rat) :
    ledgerAt (fork A p i j q) p =
      (ledgerAt A p).erase (i, q) ++ [(i, q / 2), (j, q / 2)] := by
  rw [fork, ledgerAt_updateLedger_self]

/-- Joining two halves replaces their entries at the node by the joined loan. -/
theorem ledgerAt_join {d : Layout} (A : Account d) (p : Path d) (i j : Nat) (q : Rat) :
    ledgerAt (join A p i j q) p =
      ((ledgerAt A p).erase (i, q / 2)).erase (j, q / 2) ++ [(i, q)] := by
  rw [join, ledgerAt_updateLedger_self]

/-- Lending raises a ledger by one entry, so the held fraction falls by exactly
the loan. -/
theorem held_append_singleton (l : Ledger) (i : Nat) (q : Rat) :
    Scidonia.FracPerm.Ledger.held (l ++ [(i, q)]) = Scidonia.FracPerm.Ledger.held l - q := by
  simp only [Scidonia.FracPerm.Ledger.held, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil]
  grind

/-- Lending two fractions lowers the held fraction by exactly their two
fractions. -/
theorem held_append_two (l : Ledger) (e₁ e₂ : Nat × Rat) :
    Scidonia.FracPerm.Ledger.held (l ++ [e₁, e₂])
      = Scidonia.FracPerm.Ledger.held l - e₁.2 - e₂.2 := by
  rw [show l ++ [e₁, e₂] = (l ++ [e₁]) ++ [e₂] from by simp, held_append_singleton,
    held_append_singleton]

/-- Appending one entry raises a ledger's sum of fractions by exactly that
entry's fraction. -/
theorem sum_append_singleton (l : Ledger) (e : Nat × Rat) :
    ((l ++ [e]).map Prod.snd).sum = (l.map Prod.snd).sum + e.2 := by
  have h := held_append_singleton l e.1 e.2
  simp only [Scidonia.FracPerm.Ledger.held] at h
  grind

/-- Appending two entries raises a ledger's sum of fractions by exactly their two
fractions. -/
theorem sum_append_two (l : Ledger) (e₁ e₂ : Nat × Rat) :
    ((l ++ [e₁, e₂]).map Prod.snd).sum = (l.map Prod.snd).sum + e₁.2 + e₂.2 := by
  have h := held_append_two l e₁ e₂
  simp only [Scidonia.FracPerm.Ledger.held] at h ⊢
  grind

/-- Erasing an entry lowers a ledger's sum of fractions by exactly that entry's
fraction. -/
theorem sum_erase_of_mem {l : Ledger} {e : Nat × Rat} (h : e ∈ l) :
    ((l.erase e).map Prod.snd).sum = (l.map Prod.snd).sum - e.2 := by
  have h' := Scidonia.FracPerm.Ledger.held_erase_of_mem h
  simp only [Scidonia.FracPerm.Ledger.held] at h' ⊢
  grind

/-- Lending a fraction lowers the held fraction at that node by exactly it. -/
theorem heldAt_lend {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat) :
    heldAt (lend A p i q) p = heldAt A p - q := by
  rw [heldAt, heldAt, ledgerAt_lend, held_append_singleton]

/-- Returning a loan raises the held fraction at that node by exactly the loan:
a returned read gives back what it took, no more and no less. -/
theorem heldAt_repay {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat)
    (h : Reads A p i q) : heldAt (repay A p i q) p = heldAt A p + q := by
  rw [heldAt, heldAt, ledgerAt_repay,
    Scidonia.FracPerm.Ledger.held_erase_of_mem h]

/-- Forking a loan leaves the node's held fraction exactly where it was: the two
halves are the one loan, and nothing enters or leaves the node. -/
theorem heldAt_fork {d : Layout} (A : Account d) (p : Path d) (i j : Nat) (q : Rat)
    (h : Reads A p i q) : heldAt (fork A p i j q) p = heldAt A p := by
  rw [heldAt, heldAt, ledgerAt_fork, held_append_two,
    Scidonia.FracPerm.Ledger.held_erase_of_mem h]
  have hh := halves_rejoin q
  grind

/-- Joining two halves leaves the node's held fraction exactly where it was: the
joined loan is the two halves, and nothing enters or leaves the node. -/
theorem heldAt_join {d : Layout} (A : Account d) (p : Path d) (i j : Nat) (q : Rat)
    (h₁ : Reads A p i (q / 2)) (h₂ : Reads A p j (q / 2)) (hij : (i, q / 2) ≠ (j, q / 2)) :
    heldAt (join A p i j q) p = heldAt A p := by
  have hne : (j, q / 2) ≠ (i, q / 2) := fun hh => hij hh.symm
  have h3 := Scidonia.FracPerm.Ledger.held_erase_of_mem (mem_erase_of_ne h₂ hne)
  have h4 := Scidonia.FracPerm.Ledger.held_erase_of_mem h₁
  rw [heldAt, heldAt, ledgerAt_join, held_append_singleton, h3, h4]
  have h5 := halves_rejoin q
  grind

/-- A ledger whose entries are distinct does not hold a loan it has erased. -/
theorem not_mem_erase_self : ∀ {l : Ledger}, l.Nodup → ∀ e : Nat × Rat, e ∉ l.erase e
  | [], _, _ => by simp
  | x :: xs, h, e => by
      rw [List.nodup_cons] at h
      by_cases hx : x = e
      · subst hx
        rw [List.erase_cons_head]
        exact h.1
      · rw [List.erase_cons_tail (by simpa [beq_iff_eq] using hx)]
        intro hmem
        rcases List.mem_cons.mp hmem with h1 | h2
        · exact hx h1.symm
        · exact not_mem_erase_self h.2 e h2

/-- A loan a node holds cannot be returned twice: after the return the node's
ledger no longer holds it. -/
theorem repay_not_mem {d : Layout} {A : Account d} {p : Path d} {i : Nat} {q : Rat}
    (h : (ledgerAt A p).Nodup) : ¬ Reads (repay A p i q) p i q := by
  rw [Reads, ledgerAt_repay]
  exact not_mem_erase_self h (i, q)

/-! ## The arithmetic of one node's shares -/

/-- A share is at least the whole only when something is wrong: the whole leaves
nothing for another reader. -/
theorem full_refuses_reader (q : Rat) (hq : 0 < q) : ¬ (1 + q ≤ (1 : Rat)) :=
  cannot_add_reader q hq

/-- Halving a valid share gives two valid halves: a fork's branches each run at
half the parent's share. -/
theorem half_share_valid {q : Rat} (hq : ValidShare q) : ValidShare (q / 2) :=
  half_valid hq

/-- Rejoining two halves restores the parent's share. -/
theorem halves_rejoin_share (q : Rat) : q / 2 + q / 2 = q := halves_rejoin q

/-- One half is a valid share. -/
theorem one_half_valid : ValidShare ((1 : Rat) / 2) :=
  half_valid ⟨by grind, by grind⟩

/-- A list of nonnegative pairs has a nonnegative sum of fractions. -/
theorem sum_snd_nonneg {l : List (Nat × Rat)} (hn : ∀ e ∈ l, 0 ≤ e.2) :
    0 ≤ (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have h1 : 0 ≤ x.2 := hn x (by simp)
      have h2 : 0 ≤ (xs.map Prod.snd).sum := ih (fun z hz => hn z (by simp [hz]))
      rw [List.map_cons, List.sum_cons]
      grind

/-- An entry of a list of nonnegative pairs has its fraction at most the list's
sum of fractions. -/
theorem le_sum_snd_of_mem {l : List (Nat × Rat)} (hn : ∀ e ∈ l, 0 ≤ e.2) {e : Nat × Rat}
    (he : e ∈ l) : e.2 ≤ (l.map Prod.snd).sum := by
  induction l with
  | nil => simp at he
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp he with h | h
      · rw [h]
        have hS : 0 ≤ (xs.map Prod.snd).sum := sum_snd_nonneg (fun z hz => hn z (by simp [hz]))
        grind
      · have h1 := ih (fun z hz => hn z (by simp [hz])) h
        have h2 : 0 ≤ x.snd := hn x (by simp)
        grind

/-- Erasing an entry of a list of nonnegative numbers does not raise the list's
sum of fractions. -/
theorem sum_erase_le {l : List (Nat × Rat)} (hn : ∀ e ∈ l, 0 ≤ e.2) (e : Nat × Rat) :
    ((l.erase e).map Prod.snd).sum ≤ (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx : 0 ≤ x.2 := hn x (by simp)
      by_cases hxe : x = e
      · rw [hxe, List.erase_cons_head, List.map_cons, List.sum_cons]
        have hS : 0 ≤ (xs.map Prod.snd).sum := sum_snd_nonneg (fun z hz => hn z (by simp [hz]))
        grind
      · rw [List.erase_cons_tail (by simpa [beq_iff_eq] using hxe), List.map_cons, List.sum_cons,
          List.map_cons, List.sum_cons]
        have h1 := ih (fun z hz => hn z (by simp [hz]))
        grind

/-- Two entries of a list of nonnegative numbers with *different* identifiers sum
to at most the list's sum: the identifiers are what make the two loans distinct
entries rather than one counted twice. -/
theorem add_le_sum_of_mem_ne {l : List (Nat × Rat)} (hn : ∀ e ∈ l, 0 ≤ e.2)
    {i j : Nat} (hij : i ≠ j) {q r : Rat} (hq : (i, q) ∈ l) (hr : (j, r) ∈ l) :
    q + r ≤ (l.map Prod.snd).sum := by
  induction l with
  | nil => simp at hq
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons]
      have hx : 0 ≤ x.snd := hn x (by simp)
      rcases List.mem_cons.mp hq with hq' | hq'
      · rcases List.mem_cons.mp hr with hr' | hr'
        · exfalso
          exact hij ((congrArg Prod.fst hq').trans (congrArg Prod.fst hr').symm)
        · have hy : x.snd = q := by rw [← hq']
          have h1 : r ≤ (xs.map Prod.snd).sum :=
            le_sum_snd_of_mem (fun z hz => hn z (by simp [hz])) hr'
          grind
      · rcases List.mem_cons.mp hr with hr' | hr'
        · have hy : x.snd = r := by rw [← hr']
          have h1 : q ≤ (xs.map Prod.snd).sum :=
            le_sum_snd_of_mem (fun z hz => hn z (by simp [hz])) hq'
          grind
        · have h1 := ih (fun z hz => hn z (by simp [hz])) hq' hr'
          grind

/-- Two distinct holders of one node fit in the whole: the sum of their shares is
at most one. -/
theorem share_fit {d : Layout} {A : Account d} (hA : ValidAccount A) {p : Path d}
    {i j : Nat} (hij : i ≠ j) {q r : Rat} (hq : Reads A p i q) (hr : Reads A p j r) :
    q + r ≤ 1 := by
  obtain ⟨hv, hsum, _⟩ := ledgerAt_valid A p hA
  have h1 := add_le_sum_of_mem_ne (fun e he => by have h := (hv e he).1; grind) hij hq hr
  grind

/-- A valid account's whole is at least any one loan: a loan never exceeds the
node it is taken from. -/
theorem share_le_one {d : Layout} {A : Account d} (hA : ValidAccount A) {p : Path d}
    {i : Nat} {q : Rat} (hq : Reads A p i q) : q ≤ 1 := by
  obtain ⟨hv, hsum, _⟩ := ledgerAt_valid A p hA
  have h1 := le_sum_snd_of_mem (fun e he => by have h := (hv e he).1; grind) hq
  grind

/-- A valid account's node lends positive fractions: every holder holds something
rather than nothing. -/
theorem node_shares_positive {d : Layout} {A : Account d} (hA : ValidAccount A)
    {p : Path d} {x : Nat × Rat} (hx : x ∈ ledgerAt A p) : 0 < x.2 :=
  ((ledgerAt_valid A p hA).1 x hx).1

/-- A valid account's node lends fractions that fit in the whole: the node's own
sum is at most one. -/
theorem node_sum_le_one {d : Layout} {A : Account d} (hA : ValidAccount A) {p : Path d} :
    ((ledgerAt A p).map Prod.snd).sum ≤ 1 :=
  (ledgerAt_valid A p hA).2.1

/-- A node held whole has no other holder: the holder's share is the whole, so no
positive fraction fits beside it. -/
theorem writer_excludes_reader {d : Layout} {A : Account d} {p : Path d} (hW : Writes A p)
    {i : Nat} {q : Rat} (hq : Reads A p i q) : False := by
  rw [Writes] at hW
  rw [Reads] at hq
  rw [hW] at hq
  exact List.not_mem_nil hq

/-! ## The subscriber path and the subtree of a path -/

/-- A node is in the subtree of a path when the path is a prefix of it. -/
def InSubtree {d : Layout} (p q : Path d) : Prop := ∃ r : Path (At p), q = Path.append p r

/-- A path is a prefix of another when the other is it extended by some steps. -/
def PrefixOf {d : Layout} (p q : Path d) : Prop := ∃ r : Path (At p), Path.append p r = q

/-- A path is its own subtree's root. -/
theorem self_inSubtree {d : Layout} (p : Path d) : InSubtree p p := by
  induction p with
  | here => exact ⟨Path.here, rfl⟩
  | left q ih => obtain ⟨r, hr⟩ := ih; exact ⟨r, congrArg Path.left hr⟩
  | right q ih => obtain ⟨r, hr⟩ := ih; exact ⟨r, congrArg Path.right hr⟩
  | index i q ih => obtain ⟨r, hr⟩ := ih; exact ⟨r, congrArg (Path.index i) hr⟩

/-- Every node of a write target's subtree is held by the target's owner: the
target's owner holds fraction one at the target and at every node below it, so no
other positive holder exists there. -/
theorem spine_writer_excludes {d : Layout} {A : Account d} {p : Path d}
    (hW : ∀ q, InSubtree p q → Writes A q) {q : Path d} (hq : InSubtree p q)
    {i : Nat} {r : Rat} (hr : Reads A q i r) : False :=
  writer_excludes_reader (hW q hq) hr

/-! ## The loans of a read

A read's borrow is a proposition, not a structure: it names the ghost identifier
the read returns its loans under, the leaf it observes, and the share it holds at
each node of the leaf's path. Its shares are accounted *per node* — the leaf's
loan is that node's, the ancestors' are their own — and every one of them is
positive. -/

/-- A read's borrow: the identifier it returns its loans under, the leaf it
observes, and the share it holds at each node of that leaf's path. Every one of
those shares is positive and is accounted at its own node. -/
def ReadLoan {d : Layout} (A : Account d) (id : Nat) (leaf : ObsPath d)
    (share : Path d → Rat) : Prop :=
  (∀ p, PrefixOf p leaf.path → 0 < share p)
    ∧ (∀ p, PrefixOf p leaf.path → Reads A p id (share p))

/-- A read holds a strictly positive share of every node it traverses and of the
leaf it observes: the read-through positivity law. -/
theorem spine_readThrough_positive {d : Layout} {A : Account d} {id : Nat}
    {leaf : ObsPath d} {share : Path d → Rat} (L : ReadLoan A id leaf share)
    {p : Path d} (hp : PrefixOf p leaf.path) : 0 < share p ∧ Reads A p id (share p) :=
  ⟨L.1 p hp, L.2 p hp⟩

/-- A read's loan at each node it traverses fits beside every *other* holder of
that node: the reader's share plus the other holder's is at most the whole. -/
theorem readThrough_fits {d : Layout} {A : Account d} (hA : ValidAccount A) {id : Nat}
    {leaf : ObsPath d} {share : Path d → Rat} (L : ReadLoan A id leaf share)
    {p : Path d} (hp : PrefixOf p leaf.path) {j : Nat} {r : Rat} (hj : j ≠ id)
    (hr : Reads A p j r) : share p + r ≤ 1 :=
  share_fit hA (fun h => hj h.symm) (L.2 p hp) hr

/-- A read's loan never exceeds the node it holds: the account's validity is what
bounds what a borrow can be. -/
theorem readThrough_le_one {d : Layout} {A : Account d} (hA : ValidAccount A) {id : Nat}
    {leaf : ObsPath d} {share : Path d → Rat} (L : ReadLoan A id leaf share)
    {p : Path d} (hp : PrefixOf p leaf.path) : share p ≤ 1 :=
  share_le_one hA (L.2 p hp)

/-! ## The validity-preserving account operations

Each operation below is a transition of the account, and each is shown to keep the
account valid and to conserve the node's own fraction. -/

/-- Lending keeps the account valid when the loan is a valid share that the node
still holds: a loan bigger than what the owner holds would overfill the node. -/
theorem lend_valid {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat)
    (hA : ValidAccount A) (hq : ValidShare q) (hfit : q ≤ heldAt A p)
    (hfresh : (i, q) ∉ ledgerAt A p) : ValidAccount (lend A p i q) := by
  refine updateLedger_valid A p _ hA ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact (ledgerAt_valid A p hA).1 x hx
    · rw [List.mem_singleton] at hx
      rw [hx]
      exact hq
  · rw [List.nodup_append]
    refine ⟨(ledgerAt_valid A p hA).2.2, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    rw [hb]
    intro hab
    exact hfresh (hab ▸ ha)
  · rw [sum_append_singleton]
    have h1 := node_sum_le_one (A := A) (p := p) hA
    rw [heldAt, Scidonia.FracPerm.Ledger.held] at hfit
    grind

/-- Returning a loan keeps the account valid: the node's ledger only loses an
entry. -/
theorem repay_valid {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat)
    (hA : ValidAccount A) : ValidAccount (repay A p i q) := by
  refine updateLedger_valid A p _ hA ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (ledgerAt_valid A p hA).1 x (List.mem_of_mem_erase hx)
  · exact (ledgerAt_valid A p hA).2.2.erase _
  · have h1 := sum_erase_le (fun e he => by
      have h := ((ledgerAt_valid A p hA).1 e he).1
      grind) (i, q)
    have h2 := node_sum_le_one (A := A) (p := p) hA
    grind

/-- Forking a holder's loan keeps the account valid: the node's own fraction is
unchanged and the two halves are valid shares. -/
theorem fork_valid {d : Layout} (A : Account d) (p : Path d) (i j : Nat) (q : Rat)
    (hA : ValidAccount A) (hq : ValidShare q) (hij : i ≠ j) (h : Reads A p i q)
    (hfi : (i, q / 2) ∉ ledgerAt A p) (hfj : (j, q / 2) ∉ ledgerAt A p) :
    ValidAccount (fork A p i j q) := by
  have hq' : ValidShare (q / 2) := half_valid hq
  refine updateLedger_valid A p _ hA ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact (ledgerAt_valid A p hA).1 x (List.mem_of_mem_erase hx)
    · rw [List.mem_cons] at hx
      rcases hx with hx | hx
      · rw [hx]; exact hq'
      · rw [List.mem_singleton] at hx
        rw [hx]; exact hq'
  · rw [List.nodup_append]
    refine ⟨(ledgerAt_valid A p hA).2.2.erase (i, q), ?_, ?_⟩
    · have hne : (i, q / 2) ≠ (j, q / 2) := fun hh => hij (Prod.mk.inj hh).1
      simp [List.nodup_cons, hne]
    · intro a ha b hb
      rw [List.mem_cons, List.mem_singleton] at hb
      have ha' : a ∈ ledgerAt A p := List.mem_of_mem_erase ha
      rcases hb with rfl | rfl
      · intro hab; exact hfi (hab ▸ ha')
      · intro hab; exact hfj (hab ▸ ha')
  · rw [sum_append_two, sum_erase_of_mem h]
    have h2 := node_sum_le_one (A := A) (p := p) hA
    have h4 := halves_rejoin q
    grind

/-- Joining two halves keeps the account valid when the joined loan is a valid
share the node does not already hold. -/
theorem join_valid {d : Layout} (A : Account d) (p : Path d) (i j : Nat) (q : Rat)
    (hA : ValidAccount A) (hq : ValidShare q) (hij : i ≠ j)
    (h₁ : Reads A p i (q / 2)) (h₂ : Reads A p j (q / 2))
    (hfresh : (i, q) ∉ ledgerAt A p) : ValidAccount (join A p i j q) := by
  have hq' : ValidShare (q / 2) := half_valid hq
  have hne : (i, q / 2) ≠ (j, q / 2) := fun hh => hij (Prod.mk.inj hh).1
  refine updateLedger_valid A p _ hA ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact (ledgerAt_valid A p hA).1 x (List.mem_of_mem_erase (List.mem_of_mem_erase hx))
    · rw [List.mem_singleton] at hx
      rw [hx]; exact hq
  · rw [List.nodup_append]
    refine ⟨((ledgerAt_valid A p hA).2.2.erase (i, q / 2)).erase (j, q / 2), by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    rw [hb]
    intro hab
    exact hfresh (hab ▸ List.mem_of_mem_erase (List.mem_of_mem_erase ha))
  · rw [sum_append_singleton, sum_erase_of_mem (mem_erase_of_ne h₂ hne.symm),
      sum_erase_of_mem h₁]
    have h2 := node_sum_le_one (A := A) (p := p) hA
    have h5 := halves_rejoin q
    grind

/-! ## The sibling witness

The witness the milestone rests on: the root's share is split between a reader
that borrows the left leaf and a writer that owns the right subtree whole. The
reader holds half of the root and half of the left leaf; the writer holds the
root's other half and fraction one at the right subtree's root, so the root sums
to one, the right subtree excludes every other holder, and the left read is
allowed. -/

/-- The witness layout: a struct of two leaves of naturals. -/
abbrev siblingLayout : Layout := .struct (.leaf .nat) (.leaf .nat)

/-- The witness layout's root path. -/
abbrev siblingRoot : Path siblingLayout := .here

/-- The witness layout's left leaf. -/
abbrev siblingLeft : Path siblingLayout := .left (.here : Path (.leaf .nat))

/-- The witness layout's right leaf. -/
abbrev siblingRight : Path siblingLayout := .right (.here : Path (.leaf .nat))

/-- The reader's identifier. -/
abbrev readerId : Nat := 0

/-- The writer's identifier. -/
abbrev writerId : Nat := 1

/-- The ledger the reader and the writer share the root with: one half each. -/
abbrev siblingRootLedger : Ledger := [(readerId, 1 / 2), (writerId, 1 / 2)]

/-- The reader's loan at the left leaf. -/
abbrev siblingLeftLedger : Ledger := [(readerId, 1 / 2)]

/-- The witness's account: half of the root for each of the reader and the
writer, half of the left leaf for the reader, and nothing lent out at the right
subtree's root, which its writer owns whole. -/
def siblingAccount : Account siblingLayout :=
  [(siblingRoot, siblingRootLedger), (siblingLeft, siblingLeftLedger), (siblingRight, [])]

/-- The witness's ledger at its root: the two halves. -/
theorem sibling_ledger_root : ledgerAt siblingAccount siblingRoot = siblingRootLedger := by
  simp [ledgerAt, siblingAccount, siblingRoot, siblingLeft, siblingRight]

/-- The witness's ledger at the left leaf: the reader's loan. -/
theorem sibling_ledger_left : ledgerAt siblingAccount siblingLeft = siblingLeftLedger := by
  simp [ledgerAt, siblingAccount, siblingRoot, siblingLeft, siblingRight]

/-- The witness's ledger at the right leaf: nothing is lent out there. -/
theorem sibling_ledger_right : ledgerAt siblingAccount siblingRight = [] := by
  simp [ledgerAt, siblingAccount, siblingRoot, siblingLeft, siblingRight]

/-- The root's ledger sums to the whole. -/
theorem sibling_root_ledger_sum : (siblingRootLedger.map Prod.snd).sum = 1 := by
  have hh : (1 : Rat) / 2 + 1 / 2 = 1 := halves_rejoin 1
  simp only [siblingRootLedger, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  grind

/-- The witness's held fraction at its root: the two halves fill it. -/
theorem sibling_held_root : heldAt siblingAccount siblingRoot = 0 := by
  rw [heldAt, sibling_ledger_root, Scidonia.FracPerm.Ledger.held, sibling_root_ledger_sum]
  grind

/-- The witness's held fraction at the right leaf: its writer owns it whole. -/
theorem sibling_held_right : heldAt siblingAccount siblingRight = 1 := by
  rw [heldAt, sibling_ledger_right, Scidonia.FracPerm.Ledger.held_nil]

/-- The root's two halves are valid shares that fit in the whole. -/
theorem siblingRootLedger_valid :
    (∀ x ∈ siblingRootLedger, ValidShare x.2) ∧ (siblingRootLedger.map Prod.snd).sum ≤ 1
      ∧ siblingRootLedger.Nodup := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [siblingRootLedger, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · rw [hx]; exact one_half_valid
    · rw [hx]; exact one_half_valid
  · rw [sibling_root_ledger_sum]; grind
  · rw [siblingRootLedger]; decide

/-- The reader's loan at the left leaf is valid. -/
theorem siblingLeftLedger_valid :
    (∀ x ∈ siblingLeftLedger, ValidShare x.2) ∧ (siblingLeftLedger.map Prod.snd).sum ≤ 1
      ∧ siblingLeftLedger.Nodup := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [siblingLeftLedger, List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [hx]; exact one_half_valid
  · have h : (siblingLeftLedger.map Prod.snd).sum = 1 / 2 := by
      simp only [siblingLeftLedger, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      grind
    rw [h]; exact one_half_valid.2
  · rw [siblingLeftLedger]; decide

/-- The witness's account is valid: every share is a positive fraction of at most
the whole, the root's two halves fit, no ledger names a loan twice and no node
appears twice. -/
theorem siblingAccount_valid : ValidAccount siblingAccount := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [siblingAccount, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact siblingRootLedger_valid
    · exact siblingLeftLedger_valid
    · exact ⟨by simp, by grind, by simp⟩
  · decide

/-- The sibling witness: a reader holds half of the common root and half of the
left leaf, a writer holds the root's other half and owns the right subtree whole,
the root is held by the two of them and the right subtree by the writer alone. -/
theorem spine_sibling_compatible :
    ValidAccount siblingAccount
      ∧ Reads siblingAccount siblingLeft readerId (1 / 2)
      ∧ Writes siblingAccount siblingRight
      ∧ heldAt siblingAccount siblingRoot = 0
      ∧ heldAt siblingAccount siblingRight = 1 := by
  refine ⟨siblingAccount_valid, ?_, ?_, ?_, ?_⟩
  · rw [Reads, sibling_ledger_left]
    simp [siblingLeftLedger]
  · exact sibling_ledger_right
  · exact sibling_held_root
  · exact sibling_held_right

/-- The writer's share of the root fits beside the reader's: the two halves of
the common spine fill it exactly. -/
theorem sibling_root_fits : (1 / 2 : Rat) + 1 / 2 ≤ 1 := by grind

/-- The writer excludes every reader of the right subtree, while the reader's
share of the left leaf stays positive: the exclusion is *at the same node*, and
does not forbid the sibling's read. -/
theorem sibling_read_allowed :
    0 < (1 / 2 : Rat)
      ∧ ¬ Reads siblingAccount siblingRight writerId (1 / 2)
      ∧ Reads siblingAccount siblingLeft readerId (1 / 2) := by
  refine ⟨by grind, ?_, ?_⟩
  · rw [Reads, sibling_ledger_right]; simp
  · rw [Reads, sibling_ledger_left]; simp [siblingLeftLedger]

/-! ## The three-holder witness

One node taken from its owner by a loan, forked between two holders, and lent
again to a third: the account is valid at every step, the node's own fraction is
conserved at every step, and the three holders hold a half, a quarter and a
quarter. -/

/-- The one-node layout the fork witness is read at. -/
abbrev nodeLayout : Layout := .leaf .nat

/-- The one-node path. -/
abbrev nodePath : Path nodeLayout := .here

/-- The one-node account: nothing is lent at the root, so its owner holds it
whole. -/
abbrev nodeAccount : Account nodeLayout := [(nodePath, [])]

/-- The one-node account is valid. -/
theorem nodeAccount_valid : ValidAccount nodeAccount := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [nodeAccount, List.mem_cons, List.not_mem_nil, or_false] at he
    rw [he]
    exact ⟨by simp, by grind, by simp⟩
  · decide

/-- The owner's fraction at the one node, before anything is lent: the whole. -/
theorem nodeAccount_held : heldAt nodeAccount nodePath = 1 := by
  rw [heldAt, ledgerAt_cons_self, Scidonia.FracPerm.Ledger.held_nil]

/-- The fraction a fork of a half gives each of its two holders. -/
theorem quarter_eq : ((1 : Rat) / 4) = 1 / 2 / 2 := by grind

/-- A fork's half is not the loan it came from. -/
theorem quarter_ne_half : ((1 : Rat) / 2 / 2) ≠ 1 / 2 := by grind

/-- The owner lends the first half to holder 0. -/
def halfAccount : Account nodeLayout := lend nodeAccount nodePath 0 (1 / 2)

/-- The one-node ledger after the first loan: holder 0 holds a half there. -/
theorem halfAccount_ledger : ledgerAt halfAccount nodePath = [(0, 1 / 2)] := by
  rw [halfAccount, ledgerAt_lend, ledgerAt_cons_self]
  rfl

/-- The first loan is admitted: half is a valid share that fits in what the owner
still holds, and nothing was lent there before. -/
theorem halfAccount_valid : ValidAccount halfAccount :=
  lend_valid nodeAccount nodePath 0 (1 / 2) nodeAccount_valid one_half_valid
    (by rw [nodeAccount_held]; exact one_half_valid.2)
    (by rw [ledgerAt_cons_self]; simp)

/-- The owner's fraction after the first loan: a half. -/
theorem halfAccount_held : heldAt halfAccount nodePath = 1 / 2 := by
  rw [heldAt, halfAccount_ledger, Scidonia.FracPerm.Ledger.held]
  grind

/-- The fork of the first half: holders 0 and 1 hold a quarter each. -/
def forkAccount : Account nodeLayout := fork halfAccount nodePath 0 1 (1 / 2)

/-- The one-node ledger after the fork: a quarter for each of holders 0 and 1. -/
theorem forkAccount_ledger :
    ledgerAt forkAccount nodePath = [(0, 1 / 2 / 2), (1, 1 / 2 / 2)] := by
  rw [forkAccount, ledgerAt_fork, halfAccount_ledger, List.erase_cons_head]
  rfl

/-- The first loan is where the account holds it. -/
theorem halfAccount_reads : Reads halfAccount nodePath 0 (1 / 2) := by
  show (0, 1 / 2) ∈ ledgerAt halfAccount nodePath
  rw [halfAccount_ledger]
  exact List.mem_cons_self

/-- The fork is admitted: its loan is where the account holds it, half is a valid
share, and neither half is lent there already. -/
theorem forkAccount_valid : ValidAccount forkAccount :=
  fork_valid halfAccount nodePath 0 1 (1 / 2) halfAccount_valid one_half_valid
    (by decide)
    halfAccount_reads
    (by show ((0, (1 : Rat) / 2 / 2)) ∉ ledgerAt halfAccount nodePath
        rw [halfAccount_ledger]
        simp [quarter_ne_half])
    (by show ((1, (1 : Rat) / 2 / 2)) ∉ ledgerAt halfAccount nodePath
        rw [halfAccount_ledger]
        simp [quarter_ne_half])

/-- The owner's fraction after the fork: unchanged, a half. -/
theorem forkAccount_held : heldAt forkAccount nodePath = 1 / 2 := by
  rw [heldAt, forkAccount_ledger, Scidonia.FracPerm.Ledger.held]
  have h := halves_rejoin ((1 : Rat) / 2)
  grind

/-- The second loan: holder 2 takes the other half. -/
def multiAccount : Account nodeLayout := lend forkAccount nodePath 2 (1 / 2)

/-- The three-holder ledger: a quarter for each of holders 0 and 1, and a half
for holder 2. -/
theorem multiAccount_ledger :
    ledgerAt multiAccount nodePath = [(0, 1 / 2 / 2), (1, 1 / 2 / 2), (2, 1 / 2)] := by
  rw [multiAccount, ledgerAt_lend, forkAccount_ledger]
  rfl

/-- The three-holder account is valid: one node's holders hold a half, a quarter
and a quarter, and they fit in the node. -/
theorem multiAccount_valid : ValidAccount multiAccount :=
  lend_valid forkAccount nodePath 2 (1 / 2) forkAccount_valid one_half_valid
    (by rw [forkAccount_held]; grind)
    (by show ((2, (1 : Rat) / 2)) ∉ ledgerAt forkAccount nodePath
        rw [forkAccount_ledger]
        simp)

/-- The three-holder account's node is filled: its own fraction is zero. -/
theorem multi_held_zero : heldAt multiAccount nodePath = 0 := by
  rw [heldAt, multiAccount_ledger, Scidonia.FracPerm.Ledger.held]
  have := halves_rejoin (1 / 2 : Rat)
  grind

/-- The three holders of the node: a half, a quarter and a quarter. -/
theorem multi_reads :
    Reads multiAccount nodePath 0 (1 / 4) ∧ Reads multiAccount nodePath 1 (1 / 4)
      ∧ Reads multiAccount nodePath 2 (1 / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · show ((0, (1 : Rat) / 4)) ∈ ledgerAt multiAccount nodePath
    rw [multiAccount_ledger, quarter_eq]
    exact List.mem_cons_self
  · show ((1, (1 : Rat) / 4)) ∈ ledgerAt multiAccount nodePath
    rw [multiAccount_ledger, quarter_eq]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · show ((2, (1 : Rat) / 2)) ∈ ledgerAt multiAccount nodePath
    rw [multiAccount_ledger]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The three-holder account's conservation, step by step: the first loan lowers
the owner's fraction by exactly a half, the fork leaves it where it was, and the
second loan lowers it by the second half. -/
theorem multi_conservation :
    heldAt halfAccount nodePath = heldAt nodeAccount nodePath - 1 / 2
      ∧ heldAt forkAccount nodePath = heldAt halfAccount nodePath
      ∧ heldAt multiAccount nodePath = heldAt forkAccount nodePath - 1 / 2 := by
  refine ⟨heldAt_lend nodeAccount nodePath 0 (1 / 2), ?_,
    heldAt_lend forkAccount nodePath 2 (1 / 2)⟩
  exact heldAt_fork halfAccount nodePath 0 1 (1 / 2) halfAccount_reads

end TreeOwnership

end Scidonia.RC
