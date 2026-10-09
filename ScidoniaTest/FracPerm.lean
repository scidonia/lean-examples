/-
Compile-time checks for the fractional-permission object interface
`Scidonia.FracPerm`.

These live in a separate library (`ScidoniaTest`) because they are checked by
elaboration rather than by running anything. Every rule of the interface has
an affirmative control — a program the elaborator accepts — paired with
negative checks: theorems stating that the specific obligation of a specific
program is *false*. A negative check is an ordinary proposition about
`HSt.pre` or about the closing condition of `HSt.exec`, so it cannot be
satisfied by a tactic merely failing; it is a proof that the obligation does
not hold.

`ReadTok` and `HSt` cannot be built outside the module at all, and neither
can `HSt.run` be called there, so `exec` is the only entry point. Those
negative checks state that the *elaboration* fails; `#guard_msgs` pins the
elaborator's exact message, so such a check fails both if the construction
starts being accepted and if it starts failing for some other reason.

The object of the programs here is the `Array` instance, whose behaviour is
the array interface's unchanged; the counter instance has its own section at
the end. A program names the object once, on its first primitive, and the
rest of the program is typed from it — the interface cannot guess which
object a bare `read` or `write` is for, since a program may use any of them.
-/
import Scidonia.FracPerm

open Scidonia.FracPerm
open Scidonia.FracPerm.HSt

/-! ## Tokens for the negative checks

The only way to obtain a `ReadTok` is to run an `acquire`: the constructor is
private, and so is the `HSt` accessor, so these helper definitions obtain a
token by `exec`ing a program that acquires one and gives it back. They give
the negative checks a name for the outstanding read they reason about.

A token's type does not mention the object being read: `ReadTok n q` names a
ledger entry, and the ledger is the interface's alone. The helpers are
therefore polymorphic in the object, and the counter's checks share them with
the array's. -/

/-- A token of a third, acquired and given back. -/
def acquiredThird {σ : Type} (s : σ) : ReadTok 0 (1 / 3) :=
  ((acquire 0 (1 / 3) >>>= fun t => release t >>>= fun _ => ret t).exec s
    (by hst_vc) (by hst_vc)).1

/-- A token of a half, acquired and given back. -/
def acquiredHalf {σ : Type} (s : σ) : ReadTok 0 (1 / 2) :=
  ((acquire 0 (1 / 2) >>>= fun t => release t >>>= fun _ => ret t).exec s
    (by hst_vc) (by hst_vc)).1

/-! ## Positive checks -/

/-- The program of P1: write, lend out a third and two thirds, read, give
both fractions back, and write again. The whole permission round trip. -/
def p1Prog :=
  write (σ := Array Nat) (0, 7) >>>= fun _ =>
  acquire 0 (1 / 3) >>>= fun t₁ =>
  acquire 1 (2 / 3) >>>= fun t₂ =>
  read t₁ 0 >>>= fun v =>
  release t₁ >>>= fun _ =>
  release t₂ >>>= fun _ =>
  write (0, 9) >>>= fun _ =>
  ret v

/-- P1: the program runs from the empty ledger. Its result is the value read
before the second write, and the array it leaves behind. -/
def p1Result : Option Nat × Array Nat := p1Prog.exec #[0, 0] (by hst_vc) (by hst_vc)

#guard p1Result == (some 7, #[9, 0])

/-- The program of P2: read a third out, read with it, give it back, then
write. -/
def p2Prog :=
  acquire (σ := Array Nat) 0 (1 / 3) >>>= fun t =>
  read t 1 >>>= fun _ =>
  release t >>>= fun _ =>
  write (0, 5) >>>= fun _ =>
  ret ()

/-- P2: the program runs and the write succeeds after the read was returned. -/
def p2Result : Unit × Array Nat := p2Prog.exec #[0, 0] (by hst_vc) (by hst_vc)

#guard p2Result == ((), #[5, 0])

/-! ## Negative checks -/

/-- The program of N1: lend out a third, then write. The write's precondition
is `held = 1`, which the acquisition has just made false. -/
def n1Prog := acquire (σ := Array Nat) 0 (1 / 3) >>>= fun _ => write (0, 7)

/-- N1: the precondition of the program is false at the empty ledger, because
the continuation's obligation — the write's precondition at the ledger the
acquisition leaves behind — cannot be met. -/
theorem n1_write_while_read_outstanding (a : Array Nat) : ¬ pre n1Prog [] a := by
  intro h
  have hw : Ledger.held [(0, 1 / 3)] = 1 :=
    h.right (acquiredThird a) [(0, 1 / 3)] a ⟨rfl, rfl⟩
  simp [Ledger.held] at hw
  grind

/-- The program of N2: lend out a third and give the same token back twice. -/
def n2Prog :=
  acquire (σ := Array Nat) 0 (1 / 3) >>>= fun t => release t >>>= fun _ => release t

/-- N2: the precondition is false at the empty ledger. The first `release`
consumes the ledger entry, so the second one's precondition — the entry is
present — fails. -/
theorem n2_release_twice (a : Array Nat) : ¬ pre n2Prog [] a := by
  intro h
  have h1 := h.right (acquiredThird a) [(0, 1 / 3)] a ⟨rfl, rfl⟩
  have h2 := h1.right () _ a ⟨rfl, rfl⟩
  simp [List.erase_cons_head] at h2

/-- The program of N3: lend out a third, give the token back, then read with
it. -/
def n3Prog :=
  acquire (σ := Array Nat) 0 (1 / 3) >>>= fun t => release t >>>= fun _ => read t 0

/-- N3: the precondition is false at the empty ledger. The token still exists
— values can be copied — but its ledger entry is gone, so the read's
precondition fails. -/
theorem n3_read_with_returned_token (a : Array Nat) : ¬ pre n3Prog [] a := by
  intro h
  have h1 := h.right (acquiredThird a) [(0, 1 / 3)] a ⟨rfl, rfl⟩
  have h2 := h1.right () _ a ⟨rfl, rfl⟩
  simp [List.erase_cons_head] at h2

/-- The program of N4: lend out a half, then try to lend out two thirds. -/
def n4Prog :=
  acquire (σ := Array Nat) 0 (1 / 2) >>>= fun _ => acquire 1 (2 / 3)

/-- N4: the precondition is false at the empty ledger. Once a half is out,
the held fraction is a half, so the two-thirds read's precondition fails. -/
theorem n4_overcommit (a : Array Nat) : ¬ pre n4Prog [] a := by
  intro h
  have h1 := h.right (acquiredHalf a) [(0, 1 / 2)] a ⟨rfl, rfl⟩
  have hq : (2 / 3 : Rat) ≤ Ledger.held [(0, 1 / 2)] := h1.right.right
  simp [Ledger.held] at hq
  grind

/-- The program of N4b: lend out two thirds under the same ghost id twice. -/
def n4bProg :=
  acquire (σ := Array Nat) 0 (1 / 3) >>>= fun _ => acquire 0 (1 / 3)

/-- N4b: the precondition is false at the empty ledger, because the id of the
second acquisition is already in the ledger. -/
theorem n4b_reused_ghost_id (a : Array Nat) : ¬ pre n4bProg [] a := by
  intro h
  have h1 := h.right (acquiredThird a) [(0, 1 / 3)] a ⟨rfl, rfl⟩
  simp at h1

/-- The program of N5: lend out a third and never give it back. -/
def n5Prog := acquire (σ := Array Nat) 0 (1 / 3) >>>= fun _ => ret ()

/-- N5: the closing condition `exec` demands is false for this program: at the
end of it the ledger still records the outstanding third, so the held
fraction is not `1`. -/
theorem n5_unreturned_read (a : Array Nat) :
    ¬ (∀ b l' a', HSt.post n5Prog [] a b l' a' → l'.held = 1) := by
  intro h
  have hpost : HSt.post n5Prog [] a () [(0, 1 / 3)] a :=
    ⟨acquiredThird a, [(0, 1 / 3)], a, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  have h1 := h () [(0, 1 / 3)] a hpost
  simp [Ledger.held] at h1
  grind

/-! ## Constructor checks

Both types below are reached only through the primitives of the interface:
their constructors are private, so there is no way to build a token or a
program from outside the module. Each check pins the message the elaborator
produces.

The `{...}` notation is overloaded: when it cannot be read as a structure
instance it also tries `EmptyCollection`, so on a field-less structure like
`ReadTok` the message reports both attempts. That message is pinned as it
stands; the private-constructor part of it is the failure that matters. -/

/- N6a: `ReadTok` cannot be built with the anonymous constructor. -/
/--
error: Invalid `⟨...⟩` notation: Constructor for `Scidonia.FracPerm.ReadTok` is marked as private
-/
#guard_msgs in
example : ReadTok 0 (1 / 3) := ⟨⟩

/- N6b: `ReadTok` cannot be built with structure-instance syntax either. -/
/--
error: overloaded, errors ⏎
  failed to synthesize instance of type class
    EmptyCollection (ReadTok 0 (1 / 3))
  
  Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
  
  invalid {...} notation, constructor for `ReadTok` is marked as private
-/
#guard_msgs in
example : ReadTok 0 (1 / 3) := {}

/- N7a: `HSt` cannot be built with the anonymous constructor. -/
/--
error: Invalid `⟨...⟩` notation: Constructor for `Scidonia.FracPerm.HSt` is marked as private
-/
#guard_msgs in
example : HSt (Array Nat) (fun _ _ => True) Unit (fun _ _ _ _ _ => True) :=
  ⟨fun _ _ => ⟨((), #[]), fun _ _ => ⟨[], trivial⟩⟩⟩

/- N7b: `HSt` cannot be built with structure-instance syntax either. -/
/--
error: invalid {...} notation, constructor for `HSt` is marked as private
-/
#guard_msgs in
example : HSt (Array Nat) (fun _ _ => True) Unit (fun _ _ _ _ _ => True) :=
  { run := fun _ _ => ⟨((), #[]), fun _ _ => ⟨[], trivial⟩⟩ }

/-! ## Entry point

`exec` is the only way for client code to run a program. The `HSt.run`
accessor is private, and it demands a `Cap`: a capability whose constructor
is private too, and which is a `Prop`, so it is erased and costs nothing at
run time. A client that reaches the accessor through the structure's
eliminators therefore still cannot apply it, and so cannot hand in a ledger
of its own — a fresh empty one alongside an outstanding read, say, or one
whose negative fraction cancels the outstanding amount. -/

/- N8: a client cannot call `HSt.run`, even while holding a proof of the
precondition. -/
/--
error: Field `run` from structure `Scidonia.FracPerm.HSt` is private
-/
#guard_msgs in
example (a : Array Nat) (h : ∃ l, (write (σ := Array Nat) (0, 1)).pre l a) : Unit × Array Nat :=
  (write (σ := Array Nat) (0, 1)).run a h

/- N9: the structure's eliminators do expose the accessor, but applying it
needs the capability, which cannot be produced here. -/
/--
error: Application type mismatch: The argument
  a
has type
  Array Nat
of sort `Type` but is expected to have type
  Scidonia.FracPerm.Cap✝
of sort `Prop` in the application
  run a
-/
#guard_msgs in
example (m : HSt (Array Nat) (fun l _ => Ledger.held l = 1) Unit
    (fun l s _ l' s' => l' = l ∧ s' = s.set! 0 1))
    (a : Array Nat) (h : ∃ l, Ledger.held l = 1) : Unit × Array Nat :=
  HSt.casesOn m (motive := fun _ => Unit × Array Nat) (fun run => (run a h).1)

/-- N8's affirmative control: the same program runs through `exec`, which
starts at the empty ledger and requires the closing proof. -/
def writeControl : Unit × Array Nat :=
  (write (σ := Array Nat) (0, 1)).exec #[0] (by hst_vc) (by hst_vc)

#guard writeControl == ((), #[1])

/-! ## Scoped reads

`withRead n q body` lends out the fraction, runs `body` with the token, gives
the fraction back and returns the body's result. W1 is the affirmative
control; W2 and W3 are the two ways a body can misuse the scope. -/

/-- W1's program: read inside the scope, then write once the scope has given
the fraction back. -/
def w1Prog :=
  withRead (σ := Array Nat) 0 (1 / 3) (fun t => read t 1) >>>= fun v =>
  write (0, 9) >>>= fun _ =>
  ret v

/-- W1: the scope returns the fraction on its own, so the write after it is
accepted, and the value read inside is the program's result. -/
def w1Result : Option Nat × Array Nat := w1Prog.exec #[0, 0] (by hst_vc) (by hst_vc)

#guard w1Result == (some 0, #[9, 0])

/-- The program of W2: `release` the token inside the scope, so that the
scope's own `release`, at the end, finds no entry to give back. -/
def w2Prog :=
  withRead (σ := Array Nat) 0 (1 / 3) (fun t => release t)

/-- W2: the precondition is false at the empty ledger: reaching the scope's
`release` requires the entry the body's own `release` removed. -/
theorem w2_release_inside_scope (a : Array Nat) : ¬ pre w2Prog [] a := by
  intro h
  have h1 := h.2 [(0, 1 / 3)] a ⟨rfl, rfl⟩
  have h2 : (0, 1 / 3) ∈ (([(0, 1 / 3)] : Ledger).erase (0, 1 / 3)) :=
    h1.2 () (([(0, 1 / 3)] : Ledger).erase (0, 1 / 3)) a ⟨rfl, rfl⟩
  simp [List.erase_cons_head] at h2

/-- The body of W3's scope: return the token. Its result is the scope's own
token — a `ReadTok` has one value — and the postcondition says only that the
ledger and the state are untouched, which is what lets the token escape
without the scope noticing. -/
def w3Body : (t : ReadTok 0 (1 / 3)) → HSt (Array Nat) (fun _ _ => True) (ReadTok 0 (1 / 3))
    (fun l s _ l' s' => l' = l ∧ s' = s) :=
  fun t => (ret t).conseq (fun _ _ _ => trivial) (fun _ _ _ _ _ h => ⟨h.1, h.2.1⟩)

/-- The program of W3: the scope hands the token back as its result, and the
continuation reads with it, after the scope has given the fraction back. -/
def w3Prog :=
  withRead (σ := Array Nat) 0 (1 / 3) w3Body >>>= fun t =>
  read t 0 >>>= fun _ =>
  ret ()

/-- W3: the precondition is false at the empty ledger. The scope's post leaves
the ledger the body left with the scope's entry erased, and the body left the
entry in place, so the escaped token's entry is absent where the continuation
reads — the token is dead. -/
theorem w3_escaped_token (a : Array Nat) : ¬ pre w3Prog [] a := by
  have hpost : HSt.post (withRead (σ := Array Nat) 0 (1 / 3) w3Body) [] a (acquiredThird a)
      (([(0, 1 / 3)] : Ledger).erase (0, 1 / 3)) a :=
    ⟨[(0, 1 / 3)], a, acquiredThird a, [(0, 1 / 3)], a, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
  intro h
  have h2 : (0, 1 / 3) ∈ (([(0, 1 / 3)] : Ledger).erase (0, 1 / 3)) :=
    (h.2 (acquiredThird a) _ a hpost).1
  simp [List.erase_cons_head] at h2

/-! ## The counter instance

`Counter` is a structure with a count and an array field. C1's program
reads both fields under one token and writes once the token is returned; its
negative check is the same write with the token still out. -/

/-- C1's program: bump, read the count and a log entry under one token, give
the fraction back, record, and bump again. -/
def c1Prog :=
  write (σ := Counter) Counter.WriteOp.bump >>>= fun _ =>
  acquire 0 (1 / 3) >>>= fun t =>
  read t Counter.ReadOp.hits >>>= fun hits =>
  read t (Counter.ReadOp.entry 0) >>>= fun entry =>
  release t >>>= fun _ =>
  write (Counter.WriteOp.record 7) >>>= fun _ =>
  write Counter.WriteOp.bump >>>= fun _ =>
  ret (hits, entry)

/-- C1: the counter's program runs, and its writes take effect once the read
is returned. -/
def c1Result : (Nat × Option Nat) × Counter :=
  c1Prog.exec { hits := 0, log := #[10, 20] } (by hst_vc) (by hst_vc)

#guard (c1Result.1, c1Result.2.hits, c1Result.2.log) == ((1, some 10), 2, #[10, 20, 7])

/-- The program of the counter's negative check: read the count out, then
write while the token is still out. -/
def c1ReadOutProg :=
  acquire (σ := Counter) 0 (1 / 3) >>>= fun t => read t Counter.ReadOp.hits >>>= fun _ => write Counter.WriteOp.bump

/-- C1's negative check: the precondition is false at the empty ledger,
because the write needs the whole counter and the read still holds a third of
it. -/
theorem c1_write_while_read_out (s : Counter) : ¬ pre c1ReadOutProg [] s := by
  intro h
  have h1 := h.right (acquiredThird s) [(0, 1 / 3)] s ⟨rfl, rfl⟩
  have hw : Ledger.held [(0, 1 / 3)] = 1 := h1.right _ [(0, 1 / 3)] s ⟨rfl, rfl, rfl⟩
  simp [Ledger.held] at hw
  grind
