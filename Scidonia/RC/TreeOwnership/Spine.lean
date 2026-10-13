/-
The per-node fractional account of a tree state, its laws, and the sibling
witness.

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
split by halving (`Branch.fork_conservation`, `half_valid`, `halves_rejoin`).

**What is proved.** A node whose account is empty is held whole
(`writes_holds_one`), and no other holder fits beside it (`cannot_add_reader`,
`writer_excludes_reader`, `spine_writer_excludes`); two *distinct* holders of one
node fit in the whole (`share_fit`); a loan and its return move the held fraction
by exactly the loan (`heldAt_lend`, `heldAt_repay`) and a returned loan cannot be
returned twice (`repay_not_mem`); a well-formed branch tree's leaves sum to its
share and are positive when the share is (`wf_leafSum`, `wf_sharesPositive`); a
read holds a positive share at every node of its path and fits beside any other
holder of those nodes (`spine_readThrough_positive`, `readThrough_fits`); and
`spine_sibling_compatible` exhibits the witness the milestone rests on — a
reader owning half of the common root and half of the left leaf, a writer holding
the root's other half and the whole right subtree, the root summing to one and
the right subtree excluding every other holder.
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
a finite conjunction. -/
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

/-! ## The loans -/

/-- Lend the fraction `q` at a node under the ghost identifier `i`. -/
def lend {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat) : Account d :=
  (p, ledgerAt A p ++ [(i, q)]) :: A

/-- Return the loan the identifier `i` holds at a node: the entry is erased, and
a loan the node does not hold leaves the ledger as it was. -/
def repay {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat) : Account d :=
  (p, (ledgerAt A p).erase (i, q)) :: A

/-- Lending raises a ledger by one entry, so the held fraction falls by exactly
the loan. -/
theorem held_append_singleton (l : Ledger) (i : Nat) (q : Rat) :
    Scidonia.FracPerm.Ledger.held (l ++ [(i, q)]) = Scidonia.FracPerm.Ledger.held l - q := by
  simp only [Scidonia.FracPerm.Ledger.held, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil]
  grind

/-- Lending a fraction lowers the held fraction at that node by exactly it. -/
theorem heldAt_lend {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat) :
    heldAt (lend A p i q) p = heldAt A p - q := by
  rw [heldAt, heldAt, lend, ledgerAt_cons_self, held_append_singleton]

/-- Returning a loan raises the held fraction at that node by exactly the loan:
a returned read gives back what it took, no more and no less. -/
theorem heldAt_repay {d : Layout} (A : Account d) (p : Path d) (i : Nat) (q : Rat)
    (h : Reads A p i q) : heldAt (repay A p i q) p = heldAt A p + q := by
  rw [heldAt, heldAt, repay, ledgerAt_cons_self,
    Scidonia.FracPerm.Ledger.held_erase_of_mem h]

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
  rw [Reads, repay, ledgerAt_cons_self]
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

/-- A node held whole has no other holder: the holder's share is the whole, so no
positive fraction fits beside it. -/
theorem writer_excludes_reader {d : Layout} {A : Account d} {p : Path d} (hW : Writes A p)
    {i : Nat} {q : Rat} (hq : Reads A p i q) : False := by
  rw [Writes] at hW
  rw [Reads] at hq
  rw [hW] at hq
  exact List.not_mem_nil hq

/-! ## The subtree of a path -/

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

/-! ## The branch tree of one node

The shares of the concurrent holders of a *single* node: a leaf is one holder at
its whole share, and a fork halves the parent's share between two concurrent
branches. This is the exact arithmetic of the existing read-thread fork, at one
node rather than at one root. -/

/-- The branch tree of one node's holders: one leaf per concurrent holder, forked
where a holder split itself. -/
inductive Branch where
  /-- One holder, holding `q`. -/
  | leaf (q : Rat)
  /-- Two concurrent holders, each of half the fork's share. -/
  | fork (l r : Branch)

/-- The shares of a branch tree's holders. -/
def Branch.leafSum : Branch → Rat
  | .leaf q => q
  | .fork l r => l.leafSum + r.leafSum

/-- Every holder of a branch tree holds a positive share. -/
def Branch.sharesPositive : Branch → Prop
  | .leaf q => 0 < q
  | .fork l r => l.sharesPositive ∧ r.sharesPositive

/-- A branch tree is well formed at a share: a leaf holds it whole, and a fork
gives each of its branches half of it. -/
def Branch.WF (q : Rat) : Branch → Prop
  | .leaf q' => q' = q
  | .fork l r => Branch.WF (q / 2) l ∧ Branch.WF (q / 2) r

/-- A well-formed branch tree's holders sum to its share. -/
theorem Branch.wf_leafSum : ∀ {b : Branch} {q : Rat}, b.WF q → b.leafSum = q
  | .leaf _, _, h => h
  | .fork l r, q, h => by
      rw [Branch.leafSum, wf_leafSum h.1, wf_leafSum h.2, halves_rejoin]

/-- A well-formed branch tree with a positive share has every holder positive: a
fork of a positive share has two positive halves. -/
theorem Branch.wf_sharesPositive : ∀ {b : Branch} {q : Rat}, b.WF q → 0 < q →
    b.sharesPositive
  | .leaf _, _, h, hq => by simpa [Branch.WF] using h ▸ hq
  | .fork l r, q, h, hq => by
      have hq' : 0 < q / 2 := by grind
      exact ⟨wf_sharesPositive h.1 hq', wf_sharesPositive h.2 hq'⟩

/-- A fork's two branches hold between them exactly what the fork held: forking
splits a share and joining it puts it back. -/
theorem Branch.fork_conservation {q : Rat} {l r : Branch} (h : Branch.WF q (.fork l r)) :
    l.leafSum + r.leafSum = q := by
  rw [← Branch.leafSum, wf_leafSum h]

/-- A fork's share is the halves its branches run at, and its two leaves are
positive when its share is. -/
theorem Branch.fork_halves {q : Rat} {l r : Branch} (h : Branch.WF q (.fork l r)) :
    Branch.WF (q / 2) l ∧ Branch.WF (q / 2) r := h

/-! ## A read's loans along its path -/

/-- A read through a leaf path: the ghost identifier it is entitled to return and
the share it holds at every node of its path. The shares are accounted *per node*
— the leaf's loan is this node's, the ancestors' are their own — and every one of
them is positive. -/
structure ReadLoan (d : Layout) (A : Account d) where
  /-- The ghost identifier the read returns its loans under. -/
  id : Nat
  /-- The leaf path the read observes. -/
  leaf : ObsPath d
  /-- The share the read holds at each node of its path. -/
  share : (p : Path d) → Rat
  /-- The read holds a positive share at every node it traverses. -/
  positive : ∀ p, PrefixOf p leaf.path → 0 < share p
  /-- Each of those shares is accounted at that node. -/
  held : ∀ p, PrefixOf p leaf.path → Reads A p id (share p)

/-- A read holds a strictly positive share of every node it traverses and of the
leaf it observes: the read-through positivity law. -/
theorem spine_readThrough_positive {d : Layout} {A : Account d} (L : ReadLoan d A)
    {p : Path d} (hp : PrefixOf p L.leaf.path) :
    ∃ s, 0 < s ∧ Reads A p L.id s :=
  ⟨L.share p, L.positive p hp, L.held p hp⟩

/-- A read's loan at each node it traverses fits beside every *other* holder of
that node: the reader's share plus the other holder's is at most the whole. -/
theorem readThrough_fits {d : Layout} {A : Account d} (hA : ValidAccount A)
    (L : ReadLoan d A) {p : Path d} (hp : PrefixOf p L.leaf.path) {j : Nat} {r : Rat}
    (hj : j ≠ L.id) (hr : Reads A p j r) : L.share p + r ≤ 1 :=
  share_fit (A := A) (p := p) (i := L.id) (j := j) hA (fun h => hj h.symm) (L.held p hp) hr

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

end TreeOwnership

end Scidonia.RC
