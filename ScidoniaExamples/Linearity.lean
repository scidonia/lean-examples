import Scidonia.FracPerm

/-!
# Fractional permissions by example

`Scidonia.FracPerm` gives reads of an `Array` fractional permissions. A
program is an `HArr` value built from the primitives `acquire`, `read`,
`release`, `write` and `ret`, sequenced with `>>>=`, and it is run with `exec`.
The bookkeeping lives in a ghost ledger of `(id, fraction)` entries: `acquire`
adds an entry and hands out the token that names it, `read` requires the entry
to be present, `release` removes it, and `write` requires every entry back.

The point of the exercise is that this is *not* linearity of values. Lean
values can be copied freely, and a `ReadTok n q` compiles to a constant scalar
that carries neither the id nor the fraction. A token is a *name* for the
ledger entry `(n, q)`, and the discipline is a discipline about the ledger:
every fraction taken out by `acquire` must be returned exactly once by
`release`, because only then does the held fraction come back to `1`. `exec`
starts at the empty ledger and refuses to hand back a program's result unless
the caller proves that the closing ledger holds the whole array
(`held = 1`), so a fraction still out is a program the compiler will not
accept.

Each section below states a program and one line on what it shows. An
**accepted** program is run with `exec` and its result pinned with `#guard`. A
**rejected** program comes with the compiler's refusal pinned by `#guard_msgs`
— so a reader sees the refusal, not just our word for it — and with a theorem
that the exact obligation is *false*. The theorem is the real evidence: a
tactic that fails proves nothing, while `¬ HArr.pre prog [] a` is a proposition
that cannot be met by a tactic merely giving up. The last section is honest
about what the discipline does not cover.
-/

open Scidonia.FracPerm
open Scidonia.FracPerm.HArr

/-! ## Accepted programs

Each of these `exec`s from the empty ledger and returns with every fraction
back, so the closing obligation holds and the result is a real value. -/

/-- A1: one token, several reads, returned once. Reusing a token is fine: a
ledger entry entitles its holder to read, not to read once. -/
def a1Prog :=
  acquire (α := Nat) 0 (1 / 3) >>>= fun t =>
  read t 0 >>>= fun v₀ =>
  read t 1 >>>= fun v₁ =>
  read t 0 >>>= fun _ =>
  release t >>>= fun _ =>
  ret (v₀, v₁)

/-- A1's result: the same token reads index `0` twice and index `1` once, and
the single `release` gives back the third. -/
def a1Result : (Option Nat × Option Nat) × Array Nat :=
  a1Prog.exec #[10, 20] (by harr_vc) (by harr_vc)

#guard a1Result == ((some 10, some 20), #[10, 20])

/-- A2: three readers hold `1/2`, `1/4` and `1/4` at the same time, all three
read, all three are returned and the fractions sum back to `1`, so the write
succeeds. -/
def a2Prog :=
  acquire (α := Nat) 0 (1 / 2) >>>= fun t₁ =>
  acquire 1 (1 / 4) >>>= fun t₂ =>
  acquire 2 (1 / 4) >>>= fun t₃ =>
  read t₁ 0 >>>= fun v₁ =>
  read t₂ 1 >>>= fun v₂ =>
  read t₃ 2 >>>= fun v₃ =>
  release t₁ >>>= fun _ =>
  release t₂ >>>= fun _ =>
  release t₃ >>>= fun _ =>
  write 0 99 >>>= fun _ =>
  ret (v₁, v₂, v₃)

/-- A2's result: the three concurrent reads, and the array after the write
that only becomes available once all three fractions are back. -/
def a2Result : (Option Nat × Option Nat × Option Nat) × Array Nat :=
  a2Prog.exec #[1, 2, 3] (by harr_vc) (by harr_vc)

#guard a2Result == ((some 1, some 2, some 3), #[99, 2, 3])

/-- A3: `t'` is a copy of `t`, and both are used to read. Copying the token is
harmless: it duplicates a *name*, not a permission, and the one ledger entry
is returned by the single `release`. -/
def a3Prog :=
  acquire (α := Nat) 0 (1 / 3) >>>= fun t =>
  let t' := t
  read t 0 >>>= fun v =>
  read t' 1 >>>= fun _ =>
  release t >>>= fun _ =>
  ret v

/-- A3's result: the read through the copy is served by the same entry. -/
def a3Result : Option Nat × Array Nat :=
  a3Prog.exec #[10, 20] (by harr_vc) (by harr_vc)

#guard a3Result == (some 10, #[10, 20])

/-- A4: id `0` is returned, then lent out again under the same id `0`. An id is
reserved only while its entry is in the ledger, so reuse after a return is
fine. -/
def a4Prog :=
  acquire (α := Nat) 0 (1 / 3) >>>= fun t₁ =>
  read t₁ 0 >>>= fun v₁ =>
  release t₁ >>>= fun _ =>
  acquire 0 (1 / 3) >>>= fun t₂ =>
  read t₂ 0 >>>= fun v₂ =>
  release t₂ >>>= fun _ =>
  ret (v₁, v₂)

/-- A4's result: two successive loans under the same id. -/
def a4Result : (Option Nat × Option Nat) × Array Nat :=
  a4Prog.exec #[5] (by harr_vc) (by harr_vc)

#guard a4Result == ((some 5, some 5), #[5])

/-! ## Tokens for the rejected examples

The only way to obtain a `ReadTok` is to `acquire` one, so each helper below
runs a tiny program that acquires the token and gives the fraction straight
back. The rejected examples need such a token only to name an outstanding read
in the ledger they reason about. -/

/-- A token standing for an outstanding read of a third. -/
def tokThird (a : Array Nat) : ReadTok 0 (1 / 3) :=
  ((acquire (α := Nat) 0 (1 / 3) >>>= fun t => release t >>>= fun _ => ret t).exec a
    (by harr_vc) (by harr_vc)).1

/-- A token standing for an outstanding read of a half. -/
def tokHalf (a : Array Nat) : ReadTok 0 (1 / 2) :=
  ((acquire (α := Nat) 0 (1 / 2) >>>= fun t => release t >>>= fun _ => ret t).exec a
    (by harr_vc) (by harr_vc)).1

/-- A token standing for an outstanding read of three quarters. -/
def tokThreeQuarters (a : Array Nat) : ReadTok 0 (3 / 4) :=
  ((acquire (α := Nat) 0 (3 / 4) >>>= fun t => release t >>>= fun _ => ret t).exec a
    (by harr_vc) (by harr_vc)).1

/-- A token standing for an outstanding read of a quarter, under id `1`. -/
def tokQuarter₁ (a : Array Nat) : ReadTok 1 (1 / 4) :=
  ((acquire (α := Nat) 1 (1 / 4) >>>= fun t => release t >>>= fun _ => ret t).exec a
    (by harr_vc) (by harr_vc)).1

/-- A token standing for an outstanding read of a quarter, under id `2`. -/
def tokQuarter₂ (a : Array Nat) : ReadTok 2 (1 / 4) :=
  ((acquire (α := Nat) 2 (1 / 4) >>>= fun t => release t >>>= fun _ => ret t).exec a
    (by harr_vc) (by harr_vc)).1

/-! ## Rejected programs

Each program here is one the interface must refuse. The `exec` attempt is
pinned so that a reader sees the compiler refuse it, and the theorem below it
states that the specific obligation of that specific program is false. -/

/-! ### R1: drop a read

A read is taken out and never returned, so the program does not end holding the
whole array. -/

/-- R1's program: acquire a third, read with it, and stop. -/
def r1Prog :=
  acquire (α := Nat) 0 (1 / 3) >>>= fun t =>
  read t 0 >>>= fun _ =>
  ret ()

-- R1: `exec`'s closing condition fails: the third is still out at the end.
/--
error: `grind` failed
case grind
l' : List (Nat × Rat)
a' : Array Nat
h : l' = [(0, 3⁻¹)]
x : ReadTok 0 (1 / 3)
h_1 : a' = { toList := [0] }
h_2 : ¬1 - (List.map Prod.snd l').sum = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] l' = [(0, 3⁻¹)]
    [prop] 3 * 3⁻¹ = 1
    [prop] a' = { toList := [0] }
    [prop] ¬1 - (List.map Prod.snd l').sum = 1
    [prop] List.map Prod.snd [(0, 3⁻¹)] = 3⁻¹ :: List.map Prod.snd []
    [prop] (3⁻¹ :: List.map Prod.snd []).sum = 3⁻¹ + (List.map Prod.snd []).sum
    [prop] List.map Prod.snd [] = []
    [prop] [3⁻¹].sum = 3⁻¹
    [prop] [].sum = 0
  [eqc] False propositions
    [prop] 1 - (List.map Prod.snd l').sum = 1
  [eqc] Equivalence classes
    [eqc] {l', [(0, 3⁻¹)]}
    [eqc] {a', { toList := [0] }}
    [eqc] {3⁻¹,
        (List.map Prod.snd l').sum,
        (3⁻¹ :: List.map Prod.snd []).sum,
        3⁻¹ + (List.map Prod.snd []).sum,
        [3⁻¹].sum}
    [eqc] {1, 3 * 3⁻¹, (1 - (List.map Prod.snd l').sum - 1) * (1 - (List.map Prod.snd l').sum - 1)⁻¹}
    [eqc] {List.map Prod.snd l', 3⁻¹ :: List.map Prod.snd [], List.map Prod.snd [(0, 3⁻¹)], [3⁻¹]}
    [eqc] {List.map Prod.snd [], []}
    [eqc] {(List.map Prod.snd []).sum, 0, [].sum}
  [ematch] E-matching patterns
    [thm] Vector.toArray_empty: [@Array.mk #0 (@List.nil _)]
    [thm] List.sum_singleton: [@List.sum #4 #3 #2 (@List.cons _ #0 (@List.nil _))]
    [thm] List.sum_cons: [@List.sum #4 #3 #2 (@List.cons _ #1 #0)]
    [thm] List.sum_nil: [@List.sum #2 #1 #0 (@List.nil _)]
    [thm] List.map_map: [@List.map #5 #4 #2 (@List.map #3 _ #1 #0)]
    [thm] List.map_cons: [@List.map #4 #3 #2 (@List.cons _ #1 #0)]
    [thm] List.map_nil: [@List.map #2 #1 #0 (@List.nil _)]
  [linarith] Linarith assignment for `Rat`
    [assign] (List.map Prod.snd l').sum := 10
    [assign] (3⁻¹ :: List.map Prod.snd []).sum := 10
    [assign] (List.map Prod.snd []).sum := 0
    [assign] [].sum := 0
    [assign] [3⁻¹].sum := 10
  [ring] Ring `Rat`
    [basis] Basis
      [_] 3 * 3⁻¹ + -1 = 0
      [_] 3 * (List.map Prod.snd l').sum + -3 * (List.map Prod.snd []).sum + -1 = 0
      [_] (1 - (List.map Prod.snd l').sum - 1)⁻¹ + 3 = 0
      [_] (List.map Prod.snd []).sum = 0
[grind] Diagnostics
  [ematch] E-matching Diagnostics
    [thm] Theorem Instance Count
      [thm] List.map_cons ↦ 1
      [thm] List.map_nil ↦ 1
      [thm] List.sum_cons ↦ 1
      [thm] List.sum_nil ↦ 1
      [thm] List.sum_singleton ↦ 1
-/
#guard_msgs in
example : Unit × Array Nat := r1Prog.exec #[0] (by harr_vc) (by harr_vc)

/-- R1: the closing condition `exec` demands is false for this program. The
program's own postcondition is satisfiable — with the outstanding entry still
in the ledger — and in every such state the held fraction is `2/3`, not `1`. -/
theorem r1_unreturned_read (a : Array Nat) :
    ¬ (∀ b l' a', HArr.post r1Prog [] a b l' a' → l'.held = 1) := by
  intro h
  have hpost : HArr.post r1Prog [] a () [(0, 1 / 3)] a :=
    ⟨tokThird a, [(0, 1 / 3)], a, ⟨rfl, rfl⟩,
     a[0]?, [(0, 1 / 3)], a, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  have h1 := h () [(0, 1 / 3)] a hpost
  simp [Ledger.held] at h1
  grind

/-! ### R2: return twice

The first `release` consumes the entry; the second has nothing to consume. -/

/-- R2's program: acquire a third and `release` the same token twice. -/
def r2Prog :=
  acquire (α := Nat) 0 (1 / 3) >>>= fun t =>
  release t >>>= fun _ =>
  release t

-- R2: the precondition fails at the empty ledger, so `exec` cannot start it.
/--
error: `grind` failed
case grind.2.2
h_2 : ¬∀ (x : ReadTok 0 3⁻¹), False
w : ReadTok 0 3⁻¹
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬0 < 3⁻¹ ∨ ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
    [prop] 3 * 3⁻¹ = 1
    [prop] ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
    [prop] ¬∀ (x : ReadTok 0 3⁻¹), False
  [eqc] True propositions
    [prop] ¬∀ (x : ReadTok 0 3⁻¹), False
    [prop] ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
    [prop] ¬0 < 3⁻¹ ∨ ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
  [eqc] False propositions
    [prop] ∀ (x : ReadTok 0 3⁻¹), False
  [eqc] Equivalence classes
    [eqc] {1, 3 * 3⁻¹}
  [cases] Case analyses
    [cases] [2/2]: ¬0 < 3⁻¹ ∨ ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
      [cases] source: Initial goal
    [cases] [2/2]: ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
      [cases] source: Initial goal
  [ring] Ring `Rat`
    [basis] Basis
      [_] 3 * 3⁻¹ + -1 = 0
-/
#guard_msgs in
example : Unit × Array Nat := r2Prog.exec #[0] (by harr_vc) (by harr_vc)

/-- R2: the precondition is false at the empty ledger. The first `release`
removes the entry, so the second one's precondition — the entry is present —
is false. -/
theorem r2_release_twice (a : Array Nat) : ¬ HArr.pre r2Prog [] a := by
  intro h
  have h1 := h.right (tokThird a) [(0, 1 / 3)] a ⟨rfl, rfl⟩
  have h2 := h1.right () _ a ⟨rfl, rfl⟩
  simp [List.erase_cons_head] at h2

/-! ### R3: copy, then return twice

`t'` is a copy of `t`, but a copy is not a second permission: both names resolve
to the one ledger entry, and only one of them can return it. -/

/-- R3's program: acquire a third, copy the token, and release both copies. -/
def r3Prog :=
  acquire (α := Nat) 0 (1 / 3) >>>= fun t =>
  let t' := t
  release t >>>= fun _ =>
  release t'

-- R3: as in R2, the precondition fails at the empty ledger: both copies name
-- the one entry `(0, 1/3)`, which the first `release` has already removed.
/--
error: `grind` failed
case grind.2.2
h_2 : ¬∀ (x : ReadTok 0 3⁻¹), False
w : ReadTok 0 3⁻¹
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬0 < 3⁻¹ ∨ ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
    [prop] 3 * 3⁻¹ = 1
    [prop] ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
    [prop] ¬∀ (x : ReadTok 0 3⁻¹), False
  [eqc] True propositions
    [prop] ¬∀ (x : ReadTok 0 3⁻¹), False
    [prop] ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
    [prop] ¬0 < 3⁻¹ ∨ ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
  [eqc] False propositions
    [prop] ∀ (x : ReadTok 0 3⁻¹), False
  [eqc] Equivalence classes
    [eqc] {1, 3 * 3⁻¹}
  [cases] Case analyses
    [cases] [2/2]: ¬0 < 3⁻¹ ∨ ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
      [cases] source: Initial goal
    [cases] [2/2]: ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
      [cases] source: Initial goal
  [ring] Ring `Rat`
    [basis] Basis
      [_] 3 * 3⁻¹ + -1 = 0
-/
#guard_msgs in
example : Unit × Array Nat := r3Prog.exec #[0] (by harr_vc) (by harr_vc)

/-- R3: the precondition is false at the empty ledger. Copying does not
duplicate the permission: `t'` denotes the same entry `(0, 1/3)` as `t`, which
the first `release` has already removed. -/
theorem r3_copy_release_twice (a : Array Nat) : ¬ HArr.pre r3Prog [] a := by
  intro h
  have h1 := h.right (tokThird a) [(0, 1 / 3)] a ⟨rfl, rfl⟩
  have h2 := h1.right () _ a ⟨rfl, rfl⟩
  simp [List.erase_cons_head] at h2

/-! ### R4: use after return

The token still exists as a value after `release` — values are copied, not
consumed — but its entry is gone. -/

/-- R4's program: acquire a third, release it, then read through a copy. -/
def r4Prog :=
  acquire (α := Nat) 0 (1 / 3) >>>= fun t =>
  let t' := t
  release t >>>= fun _ =>
  read t' 0

-- R4: the precondition fails at the empty ledger: the `read`'s entry `(0, 1/3)`
-- is gone, removed by the `release`.
/--
error: `grind` failed
case grind.2.2
h_2 : ¬∀ (x : ReadTok 0 3⁻¹), False
w : ReadTok 0 3⁻¹
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬0 < 3⁻¹ ∨ ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
    [prop] 3 * 3⁻¹ = 1
    [prop] ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
    [prop] ¬∀ (x : ReadTok 0 3⁻¹), False
  [eqc] True propositions
    [prop] ¬∀ (x : ReadTok 0 3⁻¹), False
    [prop] ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
    [prop] ¬0 < 3⁻¹ ∨ ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
  [eqc] False propositions
    [prop] ∀ (x : ReadTok 0 3⁻¹), False
  [eqc] Equivalence classes
    [eqc] {1, 3 * 3⁻¹}
  [cases] Case analyses
    [cases] [2/2]: ¬0 < 3⁻¹ ∨ ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
      [cases] source: Initial goal
    [cases] [2/2]: ¬3⁻¹ ≤ 1 - 0 ∨ ¬∀ (x : ReadTok 0 3⁻¹), False
      [cases] source: Initial goal
  [ring] Ring `Rat`
    [basis] Basis
      [_] 3 * 3⁻¹ + -1 = 0
-/
#guard_msgs in
example : Option Nat × Array Nat := r4Prog.exec #[0] (by harr_vc) (by harr_vc)

/-- R4: the precondition is false at the empty ledger. `t'` is still a token,
but its entry was removed by the `release`, so the `read`'s precondition — the
entry is present — is false. -/
theorem r4_read_after_release (a : Array Nat) : ¬ HArr.pre r4Prog [] a := by
  intro h
  have h1 := h.right (tokThird a) [(0, 1 / 3)] a ⟨rfl, rfl⟩
  have h2 := h1.right () _ a ⟨rfl, rfl⟩
  simp [List.erase_cons_head] at h2

/-! ### R5: write with a share still out

Two of the three fractions are returned, but a write needs all of them: the
held fraction must be exactly `1`. -/

/-- R5's program: `1/2 + 1/4 + 1/4` are lent out, the `1/2` and one `1/4` are
returned, and then a write is attempted while the last `1/4` is still out. -/
def r5Prog :=
  acquire (α := Nat) 0 (1 / 2) >>>= fun t₁ =>
  acquire 1 (1 / 4) >>>= fun t₂ =>
  acquire 2 (1 / 4) >>>= fun _ =>
  release t₁ >>>= fun _ =>
  release t₂ >>>= fun _ =>
  write 0 7

-- R5: the precondition fails at the empty ledger, and so does the closing
-- condition: the write leaves the outstanding quarter in the ledger.
/--
error: `grind` failed
case grind.2.2.2.2.2.2
h_6 : ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
w : ReadTok 0 2⁻¹
h_8 : ¬∀ (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
w_1 : ReadTok 1 4⁻¹
h_10 : ¬∀ (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
w_2 : ReadTok 2 4⁻¹
h_12 : ¬1 - (4⁻¹ + 0) = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬0 < 2⁻¹ ∨
          ¬2⁻¹ ≤ 1 - 0 ∨
            (¬∀ (x : ReadTok 0 2⁻¹), 0 < 4⁻¹) ∨
              (¬∀ (x : ReadTok 0 2⁻¹), 4⁻¹ ≤ 1 - (2⁻¹ + 0)) ∨
                (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
                  (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
                    ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] 4 * 4⁻¹ = 1
    [prop] 2 * 2⁻¹ = 1
    [prop] ¬2⁻¹ ≤ 1 - 0 ∨
          (¬∀ (x : ReadTok 0 2⁻¹), 0 < 4⁻¹) ∨
            (¬∀ (x : ReadTok 0 2⁻¹), 4⁻¹ ≤ 1 - (2⁻¹ + 0)) ∨
              (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
                (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
                  ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] (¬∀ (x : ReadTok 0 2⁻¹), 0 < 4⁻¹) ∨
          (¬∀ (x : ReadTok 0 2⁻¹), 4⁻¹ ≤ 1 - (2⁻¹ + 0)) ∨
            (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
              (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
                ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] (¬∀ (x : ReadTok 0 2⁻¹), 4⁻¹ ≤ 1 - (2⁻¹ + 0)) ∨
          (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
            (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
              ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
          (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
            ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
          ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] ¬∀ (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] ¬∀ (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] ¬1 - (4⁻¹ + 0) = 1
  [eqc] True propositions
    [prop] ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] ¬2⁻¹ ≤ 1 - 0 ∨
          (¬∀ (x : ReadTok 0 2⁻¹), 0 < 4⁻¹) ∨
            (¬∀ (x : ReadTok 0 2⁻¹), 4⁻¹ ≤ 1 - (2⁻¹ + 0)) ∨
              (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
                (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
                  ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] ¬0 < 2⁻¹ ∨
          ¬2⁻¹ ≤ 1 - 0 ∨
            (¬∀ (x : ReadTok 0 2⁻¹), 0 < 4⁻¹) ∨
              (¬∀ (x : ReadTok 0 2⁻¹), 4⁻¹ ≤ 1 - (2⁻¹ + 0)) ∨
                (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
                  (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
                    ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] (¬∀ (x : ReadTok 0 2⁻¹), 4⁻¹ ≤ 1 - (2⁻¹ + 0)) ∨
          (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
            (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
              ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] (¬∀ (x : ReadTok 0 2⁻¹), 0 < 4⁻¹) ∨
          (¬∀ (x : ReadTok 0 2⁻¹), 4⁻¹ ≤ 1 - (2⁻¹ + 0)) ∨
            (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
              (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
                ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
          ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
          (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
            ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
  [eqc] False propositions
    [prop] 1 - (4⁻¹ + 0) = 1
    [prop] ∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] ∀ (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
    [prop] ∀ (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
  [eqc] Equivalence classes
    [eqc] {1, 2 * 2⁻¹, 4 * 4⁻¹, (1 - (4⁻¹ + 0) - 1) * (1 - (4⁻¹ + 0) - 1)⁻¹}
  [cases] Case analyses
    [cases] [2/2]: ¬0 < 2⁻¹ ∨
          ¬2⁻¹ ≤ 1 - 0 ∨
            (¬∀ (x : ReadTok 0 2⁻¹), 0 < 4⁻¹) ∨
              (¬∀ (x : ReadTok 0 2⁻¹), 4⁻¹ ≤ 1 - (2⁻¹ + 0)) ∨
                (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
                  (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
                    ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
      [cases] source: Initial goal
    [cases] [2/2]: ¬2⁻¹ ≤ 1 - 0 ∨
          (¬∀ (x : ReadTok 0 2⁻¹), 0 < 4⁻¹) ∨
            (¬∀ (x : ReadTok 0 2⁻¹), 4⁻¹ ≤ 1 - (2⁻¹ + 0)) ∨
              (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
                (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
                  ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
      [cases] source: Initial goal
    [cases] [2/2]: (¬∀ (x : ReadTok 0 2⁻¹), 0 < 4⁻¹) ∨
          (¬∀ (x : ReadTok 0 2⁻¹), 4⁻¹ ≤ 1 - (2⁻¹ + 0)) ∨
            (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
              (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
                ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
      [cases] source: Initial goal
    [cases] [2/2]: (¬∀ (x : ReadTok 0 2⁻¹), 4⁻¹ ≤ 1 - (2⁻¹ + 0)) ∨
          (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
            (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
              ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
      [cases] source: Initial goal
    [cases] [2/2]: (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 0 < 4⁻¹) ∨
          (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
            ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
      [cases] source: Initial goal
    [cases] [2/2]: (¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹), 4⁻¹ ≤ 1 - (4⁻¹ + (2⁻¹ + 0))) ∨
          ¬∀ (x : ReadTok 0 2⁻¹) (x : ReadTok 1 4⁻¹) (x : ReadTok 2 4⁻¹), 1 - (4⁻¹ + 0) = 1
      [cases] source: Initial goal
  [ring] Ring `Rat`
    [basis] Basis
      [_] 2 * 2⁻¹ + -1 = 0
      [_] 4 * 4⁻¹ + -1 = 0
      [_] (1 - (4⁻¹ + 0) - 1)⁻¹ + 4 = 0
---
error: `grind` failed
case grind
l' : List (Nat × Rat)
a' : Array Nat
x : ReadTok 0 (1 / 2)
x_1 : ReadTok 1 (1 / 4)
x_2 : ReadTok 2 (1 / 4)
h : l' = [(2, 4⁻¹)]
h_1 : a' = { toList := [7] }
h_2 : ¬1 - (List.map Prod.snd l').sum = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] l' = [(2, 4⁻¹)]
    [prop] 4 * 4⁻¹ = 1
    [prop] a' = { toList := [7] }
    [prop] ¬1 - (List.map Prod.snd l').sum = 1
    [prop] List.map Prod.snd [(2, 4⁻¹)] = 4⁻¹ :: List.map Prod.snd []
    [prop] (4⁻¹ :: List.map Prod.snd []).sum = 4⁻¹ + (List.map Prod.snd []).sum
    [prop] List.map Prod.snd [] = []
    [prop] [4⁻¹].sum = 4⁻¹
    [prop] [].sum = 0
  [eqc] False propositions
    [prop] 1 - (List.map Prod.snd l').sum = 1
  [eqc] Equivalence classes
    [eqc] {l', [(2, 4⁻¹)]}
    [eqc] {a', { toList := [7] }}
    [eqc] {4⁻¹,
        (List.map Prod.snd l').sum,
        (4⁻¹ :: List.map Prod.snd []).sum,
        4⁻¹ + (List.map Prod.snd []).sum,
        [4⁻¹].sum}
    [eqc] {1, 4 * 4⁻¹, (1 - (List.map Prod.snd l').sum - 1) * (1 - (List.map Prod.snd l').sum - 1)⁻¹}
    [eqc] {List.map Prod.snd l', 4⁻¹ :: List.map Prod.snd [], List.map Prod.snd [(2, 4⁻¹)], [4⁻¹]}
    [eqc] {List.map Prod.snd [], []}
    [eqc] {(List.map Prod.snd []).sum, 0, [].sum}
  [ematch] E-matching patterns
    [thm] Vector.toArray_empty: [@Array.mk #0 (@List.nil _)]
    [thm] List.sum_singleton: [@List.sum #4 #3 #2 (@List.cons _ #0 (@List.nil _))]
    [thm] List.sum_cons: [@List.sum #4 #3 #2 (@List.cons _ #1 #0)]
    [thm] List.sum_nil: [@List.sum #2 #1 #0 (@List.nil _)]
    [thm] List.map_map: [@List.map #5 #4 #2 (@List.map #3 _ #1 #0)]
    [thm] List.map_cons: [@List.map #4 #3 #2 (@List.cons _ #1 #0)]
    [thm] List.map_nil: [@List.map #2 #1 #0 (@List.nil _)]
  [linarith] Linarith assignment for `Rat`
    [assign] (List.map Prod.snd l').sum := 10
    [assign] (4⁻¹ :: List.map Prod.snd []).sum := 10
    [assign] (List.map Prod.snd []).sum := 0
    [assign] [].sum := 0
    [assign] [4⁻¹].sum := 10
  [ring] Ring `Rat`
    [basis] Basis
      [_] 4 * 4⁻¹ + -1 = 0
      [_] 4 * (List.map Prod.snd l').sum + -4 * (List.map Prod.snd []).sum + -1 = 0
      [_] (1 - (List.map Prod.snd l').sum - 1)⁻¹ + 4 = 0
      [_] (List.map Prod.snd []).sum = 0
[grind] Diagnostics
  [ematch] E-matching Diagnostics
    [thm] Theorem Instance Count
      [thm] List.map_cons ↦ 1
      [thm] List.map_nil ↦ 1
      [thm] List.sum_cons ↦ 1
      [thm] List.sum_nil ↦ 1
      [thm] List.sum_singleton ↦ 1
-/
#guard_msgs in
example : Unit × Array Nat := r5Prog.exec #[0] (by harr_vc) (by harr_vc)

/-- R5: the precondition is false at the empty ledger. Reaching the write
requires `held = 1`, but after the two returns the held fraction is `3/4`:
`held` gives back exactly what the two `release`s put back, no more. -/
theorem r5_write_with_a_share_out (a : Array Nat) : ¬ HArr.pre r5Prog [] a := by
  intro h
  have h1 := h.right (tokHalf a) [(0, 1 / 2)] a ⟨rfl, rfl⟩
  have h2 := h1.right (tokQuarter₁ a) [(1, 1 / 4), (0, 1 / 2)] a ⟨rfl, rfl⟩
  have h3 := h2.right (tokQuarter₂ a) [(2, 1 / 4), (1, 1 / 4), (0, 1 / 2)] a ⟨rfl, rfl⟩
  have h4 := h3.right () _ a ⟨rfl, rfl⟩
  have h5 := h4.right () _ a ⟨rfl, rfl⟩
  rw [Ledger.held_erase_of_mem h4.1] at h5
  rw [Ledger.held_erase_of_mem h3.1] at h5
  simp [Ledger.held] at h5
  grind

/-! ### R6: an escaped token

A token obtained from one `exec` cannot be used by a later program: the later
program starts from its own empty ledger, in which that token's entry simply
does not appear. -/

/-- R6's token: a third, acquired and given back in one program. -/
def escapedThird (a : Array Nat) : ReadTok 0 (1 / 3) :=
  ((acquire (α := Nat) 0 (1 / 3) >>>= fun t => release t >>>= fun _ => ret t).exec a
    (by harr_vc) (by harr_vc)).1

/-- R6's program: read with the escaped token. -/
def r6Prog (a : Array Nat) :=
  read (α := Nat) (escapedThird a) 0 >>>= fun _ =>
  ret ()

-- R6: the second program starts at the empty ledger, where the escaped
-- token's entry is absent, so the precondition fails.
/--
error: `grind` failed
case grind
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
-/
#guard_msgs in
example : Unit × Array Nat := (r6Prog #[0]).exec #[0] (by harr_vc) (by harr_vc)

/-- R6: the precondition is false at the empty ledger. The escaped token's
entry `(0, 1/3)` is not in this program's ledger, so the `read`'s precondition
is false — the token is dead. -/
theorem r6_escaped_token (a : Array Nat) : ¬ HArr.pre (r6Prog a) [] a := by
  intro h
  simpa using h.1

/-! ### R7: overdraw

The fractions lent out may not exceed the whole. -/

/-- R7's program: lend out three quarters, then try to lend out a half. -/
def r7Prog :=
  acquire (α := Nat) 0 (3 / 4) >>>= fun _ =>
  acquire 1 (1 / 2)

-- R7: the precondition fails at the empty ledger, and the closing condition
-- fails too, since the program ends with both fractions still out.
/--
error: `grind` failed
case grind.2.2.2
h_3 : ¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
w : ReadTok 0 (3 * 4⁻¹)
h_5 : ¬2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬0 < 3 * 4⁻¹ ∨
          ¬3 * 4⁻¹ ≤ 1 - 0 ∨
            (¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 0 < 2⁻¹) ∨ ¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
    [prop] 2 * 2⁻¹ = 1
    [prop] 4 * 4⁻¹ = 1
    [prop] ¬3 * 4⁻¹ ≤ 1 - 0 ∨
          (¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 0 < 2⁻¹) ∨ ¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
    [prop] (¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 0 < 2⁻¹) ∨ ¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
    [prop] ¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
    [prop] ¬2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
  [eqc] True propositions
    [prop] ¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
    [prop] ¬3 * 4⁻¹ ≤ 1 - 0 ∨
          (¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 0 < 2⁻¹) ∨ ¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
    [prop] ¬0 < 3 * 4⁻¹ ∨
          ¬3 * 4⁻¹ ≤ 1 - 0 ∨
            (¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 0 < 2⁻¹) ∨ ¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
    [prop] (¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 0 < 2⁻¹) ∨ ¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
  [eqc] False propositions
    [prop] 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
    [prop] ∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
  [eqc] Equivalence classes
    [eqc] {1, 2 * 2⁻¹, 4 * 4⁻¹}
  [cases] Case analyses
    [cases] [2/2]: ¬0 < 3 * 4⁻¹ ∨
          ¬3 * 4⁻¹ ≤ 1 - 0 ∨
            (¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 0 < 2⁻¹) ∨ ¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
      [cases] source: Initial goal
    [cases] [2/2]: ¬3 * 4⁻¹ ≤ 1 - 0 ∨
          (¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 0 < 2⁻¹) ∨ ¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
      [cases] source: Initial goal
    [cases] [2/2]: (¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 0 < 2⁻¹) ∨ ¬∀ (x : ReadTok 0 (3 * 4⁻¹)), 2⁻¹ ≤ 1 - (3 * 4⁻¹ + 0)
      [cases] source: Initial goal
  [ring] Ring `Rat`
    [basis] Basis
      [_] 4 * 4⁻¹ + -1 = 0
      [_] 2 * 2⁻¹ + -1 = 0
---
error: `grind` failed
case grind
b : ReadTok 1 (1 / 2)
a : ReadTok 0 (3 / 4)
h : ¬1 - (2⁻¹ + (3 * 4⁻¹ + 0)) = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬1 - (2⁻¹ + (3 * 4⁻¹ + 0)) = 1
    [prop] 4 * 4⁻¹ = 1
    [prop] 2 * 2⁻¹ = 1
  [eqc] False propositions
    [prop] 1 - (2⁻¹ + (3 * 4⁻¹ + 0)) = 1
  [eqc] Equivalence classes
    [eqc] {1, 2 * 2⁻¹, 4 * 4⁻¹, (1 - (2⁻¹ + (3 * 4⁻¹ + 0)) - 1) * (1 - (2⁻¹ + (3 * 4⁻¹ + 0)) - 1)⁻¹}
  [ring] Ring `Rat`
    [basis] Basis
      [_] 2 * 2⁻¹ + -1 = 0
      [_] 4 * 4⁻¹ + -1 = 0
      [_] 5 * (1 - (2⁻¹ + (3 * 4⁻¹ + 0)) - 1)⁻¹ + 4 = 0

-/
#guard_msgs in
example : ReadTok 1 (1 / 2) × Array Nat := r7Prog.exec #[0] (by harr_vc) (by harr_vc)

/-- R7: the precondition is false at the empty ledger. Once three quarters are
out the held fraction is a quarter, so the half's precondition
(`1/2 ≤ held`) is false. -/
theorem r7_overdraw (a : Array Nat) : ¬ HArr.pre r7Prog [] a := by
  intro h
  have h1 := h.right (tokThreeQuarters a) [(0, 3 / 4)] a ⟨rfl, rfl⟩
  have hq : (1 / 2 : Rat) ≤ Ledger.held [(0, 3 / 4)] := h1.right.right
  simp [Ledger.held] at hq
  grind

/-! ## Honest limits

Two things are worth saying plainly about what this discipline is and is not.

A token carries no identity beyond its type `ReadTok n q`. Two tokens with the
same id and the same fraction are the same name for one ledger entry, and the
ledger cannot tell them apart. In particular, once an id has been returned and
is re-acquired, an older copy of the token refers to the *new* entry: reading
with the old copy succeeds, because the entry `(n, q)` is present again. The
accounting is still exact — the ledger has one entry, and it is returned
exactly once — but "the same token" is a statement about names, not about the
loan's history. L1 shows this.

The checks here are proofs about ghost state, and proofs can be bypassed. Code
marked `unsafe`, or an `implemented_by` override, can step outside the type
system; a program that reaches the underlying `Array` that way is not covered
by anything above. The discipline constrains what the *typed* interface allows,
and that is all it claims. -/

/-- L1: after the first loan is returned, id `0` is lent out again, and `old` —
a copy taken before the return — reads through the new entry. One entry, one
return: the accounting stays exact even though `old` outlived its loan. -/
def l1Prog :=
  acquire (α := Nat) 0 (1 / 3) >>>= fun t =>
  let old := t
  release t >>>= fun _ =>
  acquire 0 (1 / 3) >>>= fun fresh =>
  read old 0 >>>= fun v =>
  release fresh >>>= fun _ =>
  ret v

/-- L1's result: the read succeeds through the re-acquired entry. -/
def l1Result : Option Nat × Array Nat :=
  l1Prog.exec #[42] (by harr_vc) (by harr_vc)

#guard l1Result == (some 42, #[42])
