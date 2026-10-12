import Std.Tactic.BVDecide
import Std.Tactic.Do

open Std Do
set_option mvcgen.warning false

set_option doc.verso true

/-!
# The reference count, as a write sees it

This module is the counter-level vocabulary of the fractional-permission
development. It pins down what a Lean reference count is, what an increment and
a drop do to it, and the predicate a write tests before it may store in place,
so that "the write sees reference count 1" is a machine-checked predicate rather
than a sentence about the run time.

## Provenance

The model of the count — the thresholds, the kinds a count falls into,
{lit}`refCount`, the adjustments {lit}`incRefN` and {lit}`decRef`,
{lit}`markMtRc`, and the theorems that say what they mean, up to
{lit}`run_never_frees` — is vendored unchanged, names and all, from the Lean 4
repository's own machine-checked model of {lit}`lean_inc_ref_n` and
{lit}`lean_dec_ref`:

* project: {lit}`leanprover/lean4`
* file: {lit}`tests/elab/rc_model.lean`
* tag: {lit}`v4.35.0-rc3`
* licence: Apache 2.0, the Lean 4 licence

Those declarations are the Lean FRO's, not this repository's. They are
reproduced here so that this development's own facts about the count can be
stated against them, in the same proof style and on the same toolchain.
Everything after the vendored block — {lit}`IsExclusive`, {lit}`IsUnshared`, and
the facts of the final section — is this repository's addition; nothing in this
file claims authorship of the vendored declarations or their proofs.

What is *not* here: the store's run-time primitives. Taking a value out of a
store cell is an operation on the object, not on its count, so its effect on the
count is an assumption at the one place the development needs it (see
{lit}`takeOut_refCount_eq_one`), labelled as such. Whether a write escapes its
command tree, and the shape of the {lit}`Lean.IR` it emits, are later
increments.

A vendored proof's trust character is inherited with it. In this toolchain
{lit}`bv_decide` decides by native evaluation of a certificate and asserts the
result as an axiom, so a vendored theorem whose proof reaches that step carries a
generated {lit}`<theorem>._native.bv_decide.ax_1_*` beside {lit}`propext`,
{lit}`Classical.choice` and {lit}`Quot.sound`. Thirteen of the vendored block's
seventeen public theorems do; four print none — {lit}`LEAN_RC_STUCK_ST_eq`,
{lit}`incRefHugeMt_id`, {lit}`decRef_spec` and
{lit}`frozen_shared_count_stays_shared` — and of those only
{lit}`LEAN_RC_STUCK_ST_eq` invokes {lit}`bv_decide` at all, its goal having been
closed before the certificate step; the other three are {lit}`grind` and
{lit}`omega` proofs, which add no axiom. That is
inherited, not a defect to repair.

This repository's own facts use {lit}`grind`, {lit}`simp` and {lit}`decide`,
which add no axiom. A fact derived from a vendored theorem inherits that
theorem's axioms and names its source in its docstring, as
{lit}`run_never_exclusive` does.
-/

namespace Scidonia.FracPerm.StateVar
namespace RefCount
/-!
# Lean reference counting model

A model of what {lit}`lean_inc_ref_n` and {lit}`lean_dec_ref` do to a reference count, and proofs of
the properties they exist to provide: that a count tracks the references it stands for, that an
object is freed only when its last reference disappears, and that a count which cannot track them
any more (because of overflow) leaks the object rather than freeing it too early.

A count is an {name}`Int32` representing four different kinds of "counts". A positive one counts
references from the single thread that owns the object. A negative one counts them from any number
of threads, stored negated, so that an increment is a {lit}`fetch_sub`. Zero marks an object that is
never freed. And deeply negative ones are counts that over- or underflowed, which the two sticky
thresholds park there and leave alone. Most of what is proved here is about what separates those
kinds and what crosses between them.

## What is modelled, and what is not

{lit}`incRefN` and {lit}`decRef` are pure functions of the count, mirroring their C counterparts.

An increment only ever leaves a count behind, so {lit}`incRefN` yields an {name}`Int32`. A drop can
also free the object, so {lit}`decRef` yields {lit}`Option Int32`: the count left behind, or
{lit}`none` if it was freed.

{lit}`run` folds a whole sequence of those adjustments, and {lit}`runIdeal` folds the same sequence
against a {name}`Nat` reference count, which no increment can overflow and no threshold can freeze.
{lit}`run_spec` proves that {lit}`run` refines {lit}`runIdeal`.

What an adjustment decides is a function of the count alone, but running it is not one step: the
thread-shared paths test the count and only then run their {lit}`atomic_fetch_sub` or
{lit}`atomic_fetch_add`, against a count another thread may have moved in between. The last section
fractures an adjustment at that point and runs arbitrary interleavings of the halves. That costs
exactness, which survives only while no threshold has discarded an adjustment.
-/

/-- {lit}`#define LEAN_RC_STICKY      (INT_MIN + 0x10000000)` -/
abbrev LEAN_RC_STICKY : Int32 := Int32.minValue + 0x10000000

/-- {lit}`#define LEAN_RC_STICKY_DROP (INT_MIN + 0x20000000)` -/
abbrev LEAN_RC_STICKY_DROP : Int32 := Int32.minValue + 0x20000000

/-- {lit}`#define LEAN_RC_INC_MAX ((size_t)0x10000)` -/
abbrev LEAN_RC_INC_MAX : USize := 0x10000

/-- {lit}`#define LEAN_RC_STUCK_ST (INT_MIN + (int)LEAN_RC_INC_MAX)` -/
abbrev LEAN_RC_STUCK_ST : Int32 := Int32.minValue + LEAN_RC_INC_MAX.toUInt32.toInt32

/--
The value of {name}`LEAN_RC_STUCK_ST`, which {lit}`decide` cannot compute through {name}`USize`.
-/
theorem LEAN_RC_STUCK_ST_eq : LEAN_RC_STUCK_ST = Int32.minValue + 0x10000 := by
  cases System.Platform.numBits_eq <;> bv_decide

/-- {lit}`lean_is_st`. -/
abbrev isSt (rc : Int32) : Bool := rc > 0

/-- {lit}`lean_is_mt`. Note this holds of stuck counts too; they are also negative. -/
abbrev isMt (rc : Int32) : Bool := rc < 0

/-- {lit}`lean_is_persistent`. -/
abbrev isPersistent (rc : Int32) : Bool := rc == 0

/-- Stuck in the sticky range: never adjusted or freed again. -/
abbrev isStuck (rc : Int32) : Bool := rc ≤ LEAN_RC_STICKY

/-- A single-threaded count that overflowed: stuck, and still owned by one thread. -/
abbrev isStuckSt (rc : Int32) : Bool := rc ≤ LEAN_RC_STUCK_ST

/--
{lit}`is_unshared`, whether an object is owned by one thread:
```
    return rc > 0 || rc <= LEAN_RC_STUCK_ST;
```
-/
abbrev isUnshared (rc : Int32) : Bool := rc > 0 || rc ≤ LEAN_RC_STUCK_ST

/-- A thread-shared count that is not stuck, so one that still tracks references. -/
abbrev isUnstuckMt (rc : Int32) : Bool := isMt rc && !isStuck rc

/--
{lit}`lean_is_unstuck_mt` is the single comparison
{lit}`(unsigned)lean_internal_get_rc(o) > (unsigned)LEAN_RC_STICKY`: read as unsigned, a persistent,
a single-threaded and a stuck count all fall below every unstuck thread-shared count.
-/
theorem isUnstuckMt_unsigned (rc : Int32) :
    decide (rc.toUInt32 > LEAN_RC_STICKY.toUInt32) = isUnstuckMt rc := by
  bv_decide

/--
The number of references a count stands for: {lit}`rc` when single-threaded, {lit}`-rc` when
thread-shared, since a thread-shared count is stored negated. Widened, because
{lit}`-Int32.minValue` does not fit in {name}`Int32`. Signed, though no count is ever negative: the
bridges to {name}`Nat` need the count bounded on both sides, and one non-negativity hypothesis
supplies both, its upper bound coming from the type.
-/
abbrev refCount (rc : Int32) : Int64 := if isSt rc then rc.toInt64 else -rc.toInt64

/-- The same count as a {name}`Nat`: no count stands for a negative number of references. -/
abbrev refCountNat (rc : Int32) : Nat := (refCount rc).toNatClampNeg

/--
The thread-shared arm of {lit}`lean_inc_ref_huge_n`, sans concurrent semantics:
```
    while (n > 0 && lean_is_unstuck_mt(o)) {
        size_t chunk = std::min(n, LEAN_RC_INC_MAX);
        std::atomic_fetch_sub_explicit(lean_get_rc_mt_addr(o), (int)chunk, std::memory_order_relaxed);
        n -= chunk;
    }
```
-/
def incRefHugeMt (rc : Int32) (n : USize) : Int32 := Id.run do
  let mut rc := rc
  let mut n := n
  while n > 0 && rc.toUInt32 > LEAN_RC_STICKY.toUInt32 do
    let chunk := min n LEAN_RC_INC_MAX
    rc := rc - chunk.toUInt32.toInt32
    n := n - chunk
  return rc

/-- A persistent or stuck count is left alone: the loop's guard stops it before any step. -/
theorem incRefHugeMt_id (rc : Int32) (n : USize)
    (h : !(rc.toUInt32 > LEAN_RC_STICKY.toUInt32)) : incRefHugeMt rc n = rc := by
  generalize hh : incRefHugeMt rc n = r
  apply Id.of_wp_run_eq hh
  mvcgen invariants
    | inv1 => fun p => ⟨p.2.toNat⟩
    | inv2 => ⇓ x => match x with
        | .inl (rc', _) => ⌜rc' = rc ∧ ¬(rc'.toUInt32 > LEAN_RC_STICKY.toUInt32)⌝
        | .inr (rc', _) => ⌜rc' = rc⌝
  all_goals grind

/--
The loop takes the whole increment and leaves a live thread-shared count, or the count freezes.
-/
theorem incRefHugeMt_spec (rc : Int32) (n : USize) (h : isUnstuckMt rc) :
    (isUnstuckMt (incRefHugeMt rc n)
        && refCount (incRefHugeMt rc n) == refCount rc + n.toUInt64.toInt64)
      || (isStuck (incRefHugeMt rc n) && !isStuckSt (incRefHugeMt rc n)) := by
  -- Strengthened for the loop invariant: a step may land stuck, so `isUnstuckMt` would not survive
  -- as a hypothesis and `isMt` is carried instead.
  have haux : isMt rc → !isStuckSt rc →
      isMt (incRefHugeMt rc n) && !isStuckSt (incRefHugeMt rc n) &&
        (refCount (incRefHugeMt rc n) == refCount rc + n.toUInt64.toInt64
         || isStuck (incRefHugeMt rc n)) := by
    intro h hst
    generalize hh : incRefHugeMt rc n = r
    apply Id.of_wp_run_eq hh
    mvcgen invariants
      | inv1 => fun p => ⟨p.2.toNat⟩
      | inv2 => ⇓ x => match x with
          | .inl (rc', n') => ⌜isMt rc' ∧ !isStuckSt rc' ∧ (refCount rc' + n'.toUInt64.toInt64
              = refCount rc + n.toUInt64.toInt64 ∨ isStuck rc')⌝
          | .inr (rc', _) => ⌜isMt rc' ∧ !isStuckSt rc' ∧ (refCount rc'
              = refCount rc + n.toUInt64.toInt64 ∨ isStuck rc')⌝
    case vc3.pre => exact ⟨h, hst, Or.inl trivial⟩
    case vc4.post.success =>
      rename_i r' hinv
      obtain ⟨hmt, hsst, hex⟩ := hinv
      cases System.Platform.numBits_eq <;> bv_decide
    case vc2.step.isFalse =>
      rename_i b _ hg hinv
      obtain ⟨-, hmt, hsst, hex⟩ := hinv
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt] at hg
      cases System.Platform.numBits_eq <;> bv_decide
    case vc1.step.isTrue =>
      rename_i b mb rc1 n1 hg chunk rc2 n2 hinv
      obtain ⟨hvar, hmt, hsst, hex⟩ := hinv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      have hle : chunk ≤ n1 := Std.min_le_left
      have hle2 : chunk ≤ LEAN_RC_INC_MAX := Std.min_le_right
      have h1 : n2.toNat = n1.toNat - chunk.toNat := BitVec.toNat_sub_of_le hle
      have h2 : 0 < chunk.toNat := by
        show 0 < (min n1 LEAN_RC_INC_MAX).toNat
        rw [Std.min_eq_ite]; split <;> grind
      simp only [WhileVariant.eval, SVal.evalsTo] at hvar ⊢
      refine ⟨_, rfl, by grind, ?_, ?_, ?_⟩
      · cases System.Platform.numBits_eq <;> bv_decide
      · cases System.Platform.numBits_eq <;> bv_decide
      · cases System.Platform.numBits_eq <;> bv_decide
  have haux := haux (by bv_decide) (by cases System.Platform.numBits_eq <;> bv_decide)
  cases System.Platform.numBits_eq <;> bv_decide

/--
{lit}`lean_inc_ref_huge_n`:
```
    if (lean_is_st(o)) {
        int rc = lean_internal_get_rc(o);
        if (n > (size_t)(INT_MAX - rc)) lean_internal_set_rc(o, LEAN_RC_STUCK_ST);
        else                            lean_internal_set_rc(o, rc + (int)n);
    } else {
        <the loop transcribed by `incRefHugeMt` above>
    }
```
-/
abbrev incRefHugeN (rc : Int32) (n : USize) : Int32 :=
  if isSt rc then
    if n > (Int32.maxValue - rc).toUInt32.toUSize then LEAN_RC_STUCK_ST
    else rc + n.toUInt32.toInt32
  else incRefHugeMt rc n

/--
{lit}`lean_inc_ref_n(o, n)`, sans concurrent semantics:
```
    if (LEAN_UNLIKELY(n > LEAN_RC_INC_MAX)) { lean_inc_ref_huge_n(o, n); return; }
    if (LEAN_LIKELY(lean_is_st(o))) {
        lean_internal_add_rc(o, n);
    } else if (lean_is_unstuck_mt(o)) {
        std::atomic_fetch_sub_explicit(lean_get_rc_mt_addr(o), n, std::memory_order_relaxed);
    }
```
-/
abbrev incRefN (rc : Int32) (n : USize) : Int32 := Id.run do
  if n > LEAN_RC_INC_MAX then return incRefHugeN rc n
  let mut rc := rc
  if isSt rc then
    rc := rc + n.toUInt32.toInt32
  else if rc.toUInt32 > LEAN_RC_STICKY.toUInt32 then
    rc := rc - n.toUInt32.toInt32
  return rc

private theorem incRefN_eq (rc : Int32) (n : USize) :
    incRefN rc n =
      (if n > LEAN_RC_INC_MAX then incRefHugeN rc n
       else if isSt rc then rc + n.toUInt32.toInt32
       else if rc.toUInt32 > LEAN_RC_STICKY.toUInt32 then rc - n.toUInt32.toInt32
       else rc) := rfl

/--
{lit}`lean_inc_ref_n` spec: a single-threaded count takes the increment exactly or overflows into
the range {name}`isStuckSt` reserves for it, never into thread-shared. Persistent and stuck counts
are untouched. An unstuck thread-shared count takes the increment exactly or gets stuck, and either
way never wraps into the single-threaded range nor reaches {name}`isStuckSt`, so it never reads as
unshared again.
-/
theorem incRefN_spec (rc : Int32) (n : USize) :
    let rc' := incRefN rc n
    let ni := n.toUInt64.toInt64
    if isSt rc then
      (isSt rc' && refCount rc' == refCount rc + ni) || isStuckSt rc'
    else if isPersistent rc || isStuck rc then
      rc' == rc
    else
      isUnstuckMt rc
        && ((isUnstuckMt rc' && refCount rc' == refCount rc + ni)
          || (isStuck rc' && !isStuckSt rc')) := by
  -- must move `min` conditional out of `USize` for `bv_decide` to handle
  rw [incRefN_eq, incRefHugeN]
  have := incRefHugeMt_spec rc n
  have := incRefHugeMt_id rc n
  intros
  cases System.Platform.numBits_eq <;> split <;> bv_decide

/-- Drops have stopped: at or below the drop threshold. Implied by {name}`isStuck`, but wider. -/
abbrev isDropStopped (rc : Int32) : Bool := rc ≤ LEAN_RC_STICKY_DROP

/--
{lit}`lean_dec_ref_cold`, as the count it leaves behind or {lit}`none` if the object was freed:
```
    if (lean_internal_get_rc(o) != 1) {
        if (LEAN_UNLIKELY(lean_is_never_freed(o))) return;
        if (std::atomic_fetch_add_explicit(lean_get_rc_mt_addr(o), 1,
                                          std::memory_order_acq_rel) != -1) return;
    }
    <free>
```
{lit}`atomic_fetch_add` returns the count from *before* the increment, so the test that decides
whether to free is against {lit}`-1` while the count the object keeps is {lit}`0`.
-/
abbrev decRefCold (rc : Int32) : Option Int32 := Id.run do
  let mut rc := rc
  if rc != 1 then
    if rc.toUInt32 ≤ LEAN_RC_STICKY_DROP.toUInt32 then return some rc
    let old := rc
    rc := rc + 1
    if old != -1 then return some rc
  return none

/--
{lit}`lean_dec_ref`:
```
    if (LEAN_LIKELY(lean_internal_get_rc(o) > 1)) {
        lean_internal_sub_rc(o, 1);
    } else if (lean_internal_get_rc(o) != 0) {
        lean_dec_ref_cold(o);
    }
```
-/
abbrev decRef (rc : Int32) : Option Int32 :=
  if rc > 1 then some (rc - 1)
  else if rc != 0 then decRefCold rc
  else some rc

theorem decRef_spec (rc : Int32) :
    let rc' := decRef rc
    if rc > 1 then
      rc' == some (rc - 1)
    else if rc == 1 || rc == -1 then
      rc' == none
    else if rc == 0 || isDropStopped rc then
      rc' == some rc
    else
      rc' == some (rc + 1) := by
  grind

/-! ## The never-freed range -/

/-- A count no drop will ever free: persistent, or at or below the drop threshold. -/
abbrev isNeverFreed (rc : Int32) : Bool := isPersistent rc || isDropStopped rc

/--
{lit}`lean_is_never_freed` is the single comparison
{lit}`(unsigned)lean_internal_get_rc(o) <= (unsigned)LEAN_RC_STICKY_DROP`, which both drop paths
reach only once a single-threaded count is excluded. On the counts that remain it is exactly
{name}`isNeverFreed`; a single-threaded count would read as never freed too.
-/
theorem isNeverFreed_unsigned (rc : Int32) (h : !isSt rc) :
    decide (rc.toUInt32 ≤ LEAN_RC_STICKY_DROP.toUInt32) = isNeverFreed rc := by
  bv_decide

/--
Each iteration subtracts its chunk from a count the guard keeps clear of {name}`Int32.minValue`.
-/
private theorem incRefHugeMt_descends (rc : Int32) (n : USize) :
    isMt rc → incRefHugeMt rc n ≤ rc := by
  intro h
  generalize hh : incRefHugeMt rc n = r
  apply Id.of_wp_run_eq hh
  mvcgen invariants
    | inv1 => fun p => ⟨p.2.toNat⟩
    | inv2 => ⇓ x => match x with
        | .inl (rc', _) => ⌜isMt rc' ∧ rc' ≤ rc⌝
        | .inr (rc', _) => ⌜isMt rc' ∧ rc' ≤ rc⌝
  case vc3.pre => exact ⟨h, by bv_decide⟩
  case vc4.post.success =>
    rename_i r' hinv
    obtain ⟨hmt, hle⟩ := hinv
    bv_decide
  case vc2.step.isFalse =>
    rename_i b _ hg hinv
    exact hinv.2
  case vc1.step.isTrue =>
    rename_i b mb rc1 n1 hg chunk rc2 n2 hinv
    obtain ⟨hvar, hmt, hdesc⟩ := hinv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    have hle : chunk ≤ n1 := Std.min_le_left
    have hle2 : chunk ≤ LEAN_RC_INC_MAX := Std.min_le_right
    have h1 : n2.toNat = n1.toNat - chunk.toNat := BitVec.toNat_sub_of_le hle
    have h2 : 0 < chunk.toNat := by
      show 0 < (min n1 LEAN_RC_INC_MAX).toNat
      rw [Std.min_eq_ite]; split <;> grind
    simp only [WhileVariant.eval, SVal.evalsTo] at hvar ⊢
    refine ⟨_, rfl, by grind, ?_, ?_⟩
    · cases System.Platform.numBits_eq <;> bv_decide
    · cases System.Platform.numBits_eq <;> bv_decide

/-- A thread-shared increment is a {lit}`fetch_sub`, so it only ever moves the count down. -/
theorem incRefN_descends (rc : Int32) (n : USize) (h : isMt rc) : incRefN rc n ≤ rc := by
  rw [incRefN_eq, incRefHugeN]
  have := incRefHugeMt_descends rc n
  cases System.Platform.numBits_eq <;> bv_decide

/--
The never-freed range is absorbing under both adjustments: a drop leaves such a count alone, and an
increment cannot bring it back out. It does not pin the count, though: one in the band between the
two thresholds still moves under increments, just never back above the drop threshold. Only a
persistent or stuck count stops moving altogether.
-/
theorem never_freed_is_absorbing (rc : Int32) (n : USize) (h : isNeverFreed rc) :
    isNeverFreed (incRefN rc n) && decRef rc == some rc := by
  have hinc : isNeverFreed (incRefN rc n) := by
    by_cases hp : isPersistent rc
    · have hid : incRefHugeMt rc n = rc := incRefHugeMt_id rc n (by bv_decide)
      rw [incRefN_eq, incRefHugeN, hid]
      cases System.Platform.numBits_eq <;> bv_decide
    · have hdesc := incRefN_descends rc n (by bv_decide)
      cases System.Platform.numBits_eq <;> bv_decide
  grind

/--
The count {lit}`lean_mark_mt` leaves on each object it visits when sharing it with other threads.
Which objects it visits is not modelled.
```
        if (!lean_is_scalar(o) && is_unshared(o)) {
            int rc = lean_internal_get_rc(o);
            lean_internal_set_rc(o, rc < 0 || -rc <= LEAN_RC_STICKY_DROP ? LEAN_RC_STICKY : -rc);
```
-/
abbrev markMtRc (rc : Int32) : Int32 :=
  if isUnshared rc then
    if rc < 0 || -rc ≤ LEAN_RC_STICKY_DROP then LEAN_RC_STICKY else -rc
  else rc

/--
Sharing keeps the count of a single-threaded object exactly, as a live thread-shared count, unless
it overflowed or is too large for that range. Then it freezes at {name}`LEAN_RC_STICKY` rather than
wherever negating it would land, which for a count near {name}`Int32.maxValue` is in the range
{name}`isStuckSt` reserves for overflowed single-threaded counts.
-/
theorem markMtRc_spec (rc : Int32) :
    if isSt rc then
      (isUnstuckMt (markMtRc rc) && !isNeverFreed (markMtRc rc)
          && refCount (markMtRc rc) == refCount rc)
        || markMtRc rc == LEAN_RC_STICKY
    else if isStuckSt rc then
      markMtRc rc == LEAN_RC_STICKY
    else
      markMtRc rc == rc := by
  simp only [markMtRc, isUnshared, isStuckSt, LEAN_RC_STUCK_ST_eq]
  split <;> (try split) <;> (try split) <;> bv_decide

/--
A shared count never reads as unshared, so a later {lit}`lean_mark_mt` leaves the object and what it
points to alone.
-/
theorem markMtRc_shared (rc : Int32) : !isUnshared (markMtRc rc) := by
  simp only [markMtRc, isUnshared, LEAN_RC_STUCK_ST_eq]
  split <;> (try split) <;> bv_decide

/-- No drop makes a shared count read as unshared again, by {name}`decRef_spec`. -/
theorem decRef_stays_shared (rc rc' : Int32) (h : !isUnshared rc) (h' : decRef rc = some rc') :
    !isUnshared rc' := by
  have hs := decRef_spec rc
  simp only [h'] at hs
  simp only [isUnshared, LEAN_RC_STUCK_ST_eq] at h ⊢
  split at hs <;> (try split at hs) <;> (try split at hs) <;>
    simp only [beq_iff_eq, Option.some.injEq, reduceCtorEq] at hs <;> (try subst hs) <;> bv_decide

/--
An increment whose sticky check passed moves the count down by at most {name}`LEAN_RC_INC_MAX`, and
once a thread-shared count has frozen at {name}`LEAN_RC_STICKY` only such increments in flight still
move it. Short of 4095 of them the count stays clear of
{name}`isStuckSt`, so {name}`markMtRc` leaves it alone.
-/
theorem frozen_shared_count_stays_shared (rc : Int32) (k : Nat) (hk : k ≤ 4094)
    (h : LEAN_RC_STICKY.toInt - k * LEAN_RC_INC_MAX.toNat ≤ rc.toInt) : !isStuckSt rc := by
  have h1 : LEAN_RC_STICKY.toInt = -0x70000000 := by decide
  have h2 : LEAN_RC_STUCK_ST.toInt = -0x7fff0000 := by rw [LEAN_RC_STUCK_ST_eq]; decide
  have h3 : LEAN_RC_INC_MAX.toNat = 0x10000 := by
    cases System.Platform.numBits_eq <;> simp [LEAN_RC_INC_MAX, USize.toNat_ofNat, *]
  rw [h3] at h
  simp only [isStuckSt, Int32.le_iff_toInt_le, Bool.not_eq_true', decide_eq_false_iff_not,
    Int.not_le]
  omega

/-! ## Counts that cannot overflow -/

/-- Addition that stays non-negative in {name}`Int64` is addition in {name}`Nat`. -/
private theorem toNatClampNeg_add (a a' ni : Int64) (h0 : 0 ≤ a.toInt) (h1 : 0 ≤ ni.toInt)
    (h2 : a' = a + ni) (h3 : 0 ≤ a'.toInt) :
    a'.toNatClampNeg = a.toNatClampNeg + ni.toNatClampNeg := by
  have b1 := Int64.toInt_lt a
  have b3 := Int64.toInt_lt ni
  grind [Int64.toNatClampNeg, Int64.toInt_add, Int.bmod]

/-- An increment that reads as non-negative signed is the increment itself. -/
private theorem toNatClampNeg_toInt64 (n : USize) (h : 0 ≤ (n.toUInt64.toInt64).toInt) :
    (n.toUInt64.toInt64).toNatClampNeg = n.toNat := by
  have hb := USize.toNat_lt n
  grind [Int64.toNatClampNeg, Int64.toInt, UInt64.toInt64, Int64.toBitVec,
    BitVec.toInt_eq_toNat_bmod, Int.bmod]

/-- No count stands for a negative number of references, whatever range it has reached. -/
private theorem refCount_nonneg (rc : Int32) : 0 ≤ (refCount rc).toInt := by
  have h : (0 : Int64) ≤ refCount rc := by bv_decide
  simpa [Int64.le_iff_toInt_le] using h

/-- The two views agree on the last reference, which is the count a drop frees on. -/
private theorem refCountNat_eq_one (rc : Int32) : refCountNat rc = 1 ↔ refCount rc = 1 := by
  have h0 := refCount_nonneg rc
  have h1 : (1 : Int64).toInt = 1 := by decide
  grind [Int64.toNatClampNeg, Int64.toInt.inj]

/-- A single-threaded increment adds to the count, so it only ever moves up. -/
theorem incRefN_ascends (rc : Int32) (n : USize) (h : isSt rc) (h' : isSt (incRefN rc n)) :
    rc ≤ incRefN rc n := by
  rw [incRefN_eq, incRefHugeN] at h' ⊢
  cases System.Platform.numBits_eq <;> bv_decide

/--
Short of the never-freed range an increment is exact, and its amount reads the same signed as
unsigned: {name}`incRefN_ascends` and {name}`incRefN_descends` rule out the wrapped reading that
{name}`incRefN_spec` alone would leave open.
-/
private theorem incRefN_exact (rc : Int32) (n : USize) (h : !isNeverFreed (incRefN rc n)) :
    refCount (incRefN rc n) = refCount rc + n.toUInt64.toInt64
      ∧ (0 : Int64) ≤ n.toUInt64.toInt64 := by
  have hspec := incRefN_spec rc n
  have hasc := incRefN_ascends rc n
  have hdesc := incRefN_descends rc n
  refine ⟨?_, ?_⟩ <;> (cases System.Platform.numBits_eq <;> split at hspec <;> bv_decide)

/--
What {lit}`lean_inc_ref_n` does to a reference count that cannot overflow: it takes the whole
increment, exactly, or the count reaches the never-freed range. {name}`incRefN_spec` says this in
the widths the C uses, where a large enough increment wraps; over {name}`Nat` no case is excused by
width.
-/
theorem incRefN_spec_nat (rc : Int32) (n : USize) :
    isNeverFreed (incRefN rc n) || refCountNat (incRefN rc n) == refCountNat rc + n.toNat := by
  by_cases hnf : isNeverFreed (incRefN rc n)
  · simp [hnf]
  · obtain ⟨hex, hni⟩ := incRefN_exact rc n (by grind)
    have hni' : 0 ≤ (n.toUInt64.toInt64).toInt := by simpa [Int64.le_iff_toInt_le] using hni
    have hadd := toNatClampNeg_add (refCount rc) (refCount (incRefN rc n)) (n.toUInt64.toInt64)
      (refCount_nonneg rc) hni' hex (refCount_nonneg _)
    have hnn := toNatClampNeg_toInt64 n hni'
    grind

/-- A drop that does not free either leaves a never-freed count alone or removes one reference. -/
private theorem decRef_keeps (rc rc' : Int32) (h : decRef rc = some rc') :
    (isNeverFreed rc && rc' == rc)
      || (!isNeverFreed rc && refCount rc' == refCount rc - 1 && !(refCount rc == 1)) := by
  have hcold : ∀ rc : Int32, decRefCold rc =
      (if rc != 1 then
        (if rc.toUInt32 ≤ LEAN_RC_STICKY_DROP.toUInt32 then some rc
         else if rc != -1 then some (rc + 1) else none)
       else none) := fun _ => rfl
  simp only [decRef, hcold] at h
  repeat' split at h
  all_goals
    (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    (try subst h) <;> (try simp only [bne_iff_ne, ne_eq] at *) <;> bv_decide

/-- A drop frees exactly on the last reference. -/
private theorem decRef_frees_nat (rc : Int32) (h : decRef rc = none) : refCountNat rc = 1 :=
  (refCountNat_eq_one rc).mpr (by grind)

/-- {name}`decRef_keeps` over the count that cannot overflow. -/
private theorem decRef_keeps_nat (rc rc' : Int32) (h : decRef rc = some rc') :
    (isNeverFreed rc && rc' == rc)
      || (!isNeverFreed rc && refCountNat rc == refCountNat rc' + 1
            && !(refCountNat rc == 1)) := by
  have hk := decRef_keeps rc rc' h
  have hone := refCountNat_eq_one rc
  have h1 : (1 : Int64).toNatClampNeg = 1 := by decide
  by_cases hnf : isNeverFreed rc
  · have hrc : rc' = rc := by bv_decide
    simp [hnf, hrc]
  · have hex : refCount rc = refCount rc' + 1 := by bv_decide
    have hnem : ¬(refCount rc = 1) := by bv_decide
    have hadd := toNatClampNeg_add (refCount rc') (refCount rc) 1
      (refCount_nonneg rc') (by decide) hex (refCount_nonneg rc)
    grind

/-! ## Sequences of adjustments -/

/-- One adjustment: {lit}`lean_inc_ref_n(o, n)` or {lit}`lean_dec_ref(o)`. -/
inductive Op where
  | inc (n : USize)
  | dec
  deriving DecidableEq

/-- The count an adjustment leaves behind, or {lit}`none` if it freed the object. -/
abbrev Op.apply : Op → Int32 → Option Int32
  | .inc n, rc => some (incRefN rc n)
  | .dec, rc => decRef rc

/--
The same adjustment against a count that cannot overflow: an increment adds its whole amount, a drop
frees on the last reference and otherwise subtracts one.
-/
abbrev Op.applyIdeal : Op → Nat → Option Nat
  | .inc n, k => some (k + n.toNat)
  | .dec, k => if k == 1 then none else some (k - 1)

/-- A sequence of adjustments. {lit}`none` propagates: a freed object is never adjusted again. -/
def run : Option Int32 → List Op → Option Int32
  | s, [] => s
  | s, op :: ops => run (s.bind op.apply) ops

/-- The same sequence, against the count that cannot overflow. -/
def runIdeal : Option Nat → List Op → Option Nat
  | t, [] => t
  | t, op :: ops => runIdeal (t.bind op.applyIdeal) ops

/--
The relation a sequence maintains between the two counts, one row per outcome:

* the object was freed, and the count that cannot overflow agrees the last reference had gone;
* the object outlived that count reaching zero, which only a never-freed count can do;
* both are still live, and they agree exactly unless the count has reached the never-freed range.

Freeing while references remain is the combination no row admits, and it is the one the sticky range
exists to rule out.
-/
abbrev tracks : Option Int32 → Option Nat → Bool
  | none, t => t.isNone
  | some rc, none => isNeverFreed rc
  | some rc, some k => isNeverFreed rc || refCountNat rc == k

/-- One adjustment preserves {name}`tracks`, which is the whole content of {lit}`run_spec`. -/
private theorem tracks_step (op : Op) (s : Option Int32) (t : Option Nat) (h : tracks s t) :
    tracks (s.bind op.apply) (t.bind op.applyIdeal) := by
  match s, t with
  | none, none => simp
  | none, some k => simp at h
  | some rc, t =>
    have habs := never_freed_is_absorbing rc
    have hspec := incRefN_spec_nat rc
    have hfrees := decRef_frees_nat rc
    have hkeeps := decRef_keeps_nat rc
    cases op <;> cases t <;>
      simp only [tracks, Op.apply, Op.applyIdeal, Option.bind] at h ⊢ <;> grind

/-- Every sequence of adjustments maintains {name}`tracks`, from every count it can start at. -/
theorem run_spec (rc : Int32) (ops : List Op) :
    tracks (run (some rc) ops) (runIdeal (some (refCountNat rc)) ops) :=
  by
  have aux : ∀ (ops : List Op) (s : Option Int32) (t : Option Nat),
      tracks s t → tracks (run s ops) (runIdeal t ops) := by
    intro ops
    induction ops with
    | nil => exact fun _ _ h => h
    | cons op ops ih => exact fun s t h => ih _ _ (tracks_step op s t h)
  exact aux ops _ _ (by simp [tracks])

/--
Once a count reaches the never-freed range no sequence ever frees the object, however long, and it
stays in that range. This is the leak rather than crash guarantee the sticky range exists for, and
{name}`run_spec` does not give it: {name}`tracks` is satisfied when both counts have freed, and a
stuck count stands for enough references that the count that cannot overflow does reach zero, given
enough drops.
-/
theorem run_never_frees (rc : Int32) (ops : List Op) (h : isNeverFreed rc) :
    ∃ rc', run (some rc) ops = some rc' ∧ isNeverFreed rc' := by
  induction ops generalizing rc with
  | nil => exact ⟨rc, rfl, h⟩
  | cons op ops ih =>
    have habs := never_freed_is_absorbing rc
    cases op with
    | inc n => exact ih (incRefN rc n) (by grind)
    | dec =>
      show ∃ rc', run (decRef rc) ops = some rc' ∧ isNeverFreed rc'
      rw [show decRef rc = some rc by grind]
      exact ih rc h

/-! ## The two tests a write makes

The declarations up to here are vendored, as the module header says; everything
from here on is this repository's addition. A write may store in place only when
the runtime's exclusivity test holds of the count it holds the object by. The
interface has a second, weaker test, {lit}`is_unshared`, which a read may use;
the two are not interchangeable, and {lit}`ScidoniaTest/Count.lean` exhibits a
count that passes one and fails the other.
-/

/-- The runtime's {lit}`lean_is_exclusive`, which decides whether a write may
store in place: the count is single-threaded and stands for exactly one
reference.

{name}`isSt` alone is not enough. It admits a count that stands for many
references and, once the count has overflowed while single-threaded, one that
stands for no reference this count can still track; either way a second
reference exists that a store in place would lose. -/
def IsExclusive (rc : Int32) : Prop := isSt rc ∧ rc = 1

/-- The runtime's {lit}`is_unshared`, whether one thread owns the object. It is
strictly weaker than {name}`IsExclusive`: {name}`isUnshared` is
{lit}`rc > 0 || rc ≤ LEAN_RC_STUCK_ST`, so a count that overflowed while
single-threaded is unshared while standing for far more than one reference. A
write that tests {name}`IsUnshared` and then stores in place drops the other
references; the two tests are not interchangeable. -/
def IsUnshared (rc : Int32) : Prop := isUnshared rc

/-! ## The counter-level facts the discipline rests on

Each fact says what its count shape means for the write: whether the write may
store in place, or why it must copy.
-/

/-- An extra reference costs the write its in-place update: incrementing an
exclusive count by one leaves a count that is no longer exclusive. This is why a
write whose value the caller also keeps cannot be the write that stores in
place. -/
theorem not_exclusive_incRefN_one (rc : Int32) (h : IsExclusive rc) :
    ¬ IsExclusive (incRefN rc 1) := by
  obtain ⟨-, hone⟩ := h
  subst hone
  -- The increment of one: the count is single-threaded, and the increment is
  -- small, so the guard over the platform word size is the only step that does
  -- not reduce in the kernel.
  have hinc : incRefN (1 : Int32) 1 = 2 := by
    have hg : ¬ ((1 : USize) > LEAN_RC_INC_MAX) := by
      show ¬ (LEAN_RC_INC_MAX < (1 : USize))
      rw [USize.lt_iff_toNat_lt]
      simp only [LEAN_RC_INC_MAX, USize.toNat_ofNat]
      rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
    have hu : (1 : USize).toUInt32.toInt32 = 1 := by
      rw [USize.toUInt32_ofNat]
      decide
    have hst : isSt (1 : Int32) = true := by decide
    rw [incRefN_eq, ite_eq_right hg, ite_eq_left hst, hu]
    decide
  rw [hinc]
  simp only [IsExclusive, isSt, decide_eq_true_eq, not_and]
  grind

/-- Dropping the extra reference restores it: the count 2 that a hand-off leaves
drops back to 1, the exclusive count, when the cell's own reference goes. -/
theorem decRef_two (rc : Int32) (h : rc = 2) : decRef rc = some 1 := by
  subst h
  decide

/-- A thread-shared count is never exclusive, whatever single-threaded count it
came from: a write that finds one must copy. -/
theorem not_exclusive_of_isMt (rc : Int32) (h : isMt rc) : ¬ IsExclusive rc := by
  simp only [IsExclusive, isSt, isMt, decide_eq_true_eq, not_and] at h ⊢
  grind

/-- Sharing an object with other threads ({lit}`lean_mark_mt`) leaves a count
that is never exclusive. This is the {lit}`Task.spawn` measurement read off the
model: the object a spawned task receives reads as thread-shared, so a write
that meets it after a spawn cannot store in place. -/
theorem markMtRc_not_exclusive (rc : Int32) : ¬ IsExclusive (markMtRc rc) := by
  simp only [IsExclusive, isSt, markMtRc, isUnshared, LEAN_RC_STUCK_ST_eq,
    LEAN_RC_STICKY, LEAN_RC_STICKY_DROP, decide_eq_true_eq, not_and]
  split <;> (try split) <;> (try split) <;> grind

/-- A count no drop will ever free — persistent, or parked in the never-freed
range by an overflow — is never exclusive either, so a write cannot store in
place on it. -/
theorem not_exclusive_of_neverFreed (rc : Int32) (h : isNeverFreed rc) :
    ¬ IsExclusive rc := by
  simp only [IsExclusive, isSt, isNeverFreed, isPersistent, isDropStopped, decide_eq_true_eq,
    not_and, Bool.or_eq_true] at h ⊢
  rcases h with h | h <;> grind

/-- A never-freed count stays not exclusive however the write's adjustments run:
no sequence of increments and drops from one reaches an exclusive count.
{name}`run_never_frees` says the count stays in the never-freed range; this says
what that costs the write.

The proof composes that vendored theorem with {name}`not_exclusive_of_neverFreed`,
so it inherits the axioms of the vendored {name}`run_never_frees`: whatever that
proof rests on, this one rests on too, and nothing more. In this toolchain the
vendored proof rests on generated certificate axioms for the decision procedure
it uses alongside the standard kernel principles; {lit}`#print axioms` in
{lit}`ScidoniaTest/Count.lean` prints the list. -/
theorem run_never_exclusive (rc : Int32) (ops : List Op) (h : isNeverFreed rc) :
    ∃ rc', run (some rc) ops = some rc' ∧ ¬ IsExclusive rc' := by
  obtain ⟨rc', hrun, hnf⟩ := run_never_frees rc ops h
  exact ⟨rc', hrun, not_exclusive_of_neverFreed rc' hnf⟩

/-- The take-out's arithmetic: if the store cell holds the only reference
({lit}`refCount rc0 = 1`) and a take-out both hands the value to the caller and
releases the cell's own reference, the count the caller's value is left holding
is 1 — the exclusive count again, which is what makes the hand-off copy-free.

The two hypotheses are the store's contract, and they are *assumptions*: taking
a value out of a store cell is a run-time operation on the object, not a counter
operation, and this module does not model it. What is checked here is what those
two counter-level effects compose to; which cell the store holds and what its
primitive does are the caller's obligation. -/
theorem takeOut_refCount_eq_one (rc0 rc1 rc2 : Int32)
    (hcell : refCount rc0 = 1)
    (hhand : refCount rc1 = refCount rc0 + 1)
    (hrelease : refCount rc2 = refCount rc1 - 1) :
    refCount rc2 = 1 := by
  rw [hrelease, hhand, hcell]
  decide

end RefCount
end Scidonia.FracPerm.StateVar
