/-
The array as a lawful state variable, and the bridge back to the structured
interface's own trees.

`Scidonia.FracPerm.Structured` is the array interface: its `Reader.get` and
`Reader.size` observe `a[i]?` and `a.size`, its `Program.set` replaces an element
in place when the index is in bounds and leaves the array alone otherwise, and
`Executor.runFresh` is the one runner of its sealed executor. This module makes
the same array an instance of `LawfulStateVar`, so that every theorem of
`Scidonia.FracPerm.StateVar.Model` — share conservation, exclusion, replay,
schedule independence — holds of it, and then proves that the instance's
denotation of a *translated* structured tree is the structured denotation of the
original.

The translation is `liftR`/`liftP`, by structural recursion on the existing
trees; `bridge_val`/`bridge_pval` are the denotation bridges, and
`runFresh_eq_pval` composes M1's own `runFresh_eq_pval` with `bridge_pval` to
relate the shipped runner to the generic denotation. There is no second runner
and no new executor: the sealed `Reader`/`Program`/`runFresh` of the structured
interface are untouched, and public `liftR`/`liftP` reveal nothing beyond the
trees `Reader.treeOf`/`Program.treeOf` already expose.

The observation encoding is constructor-faithful: a `get` observes
`.none`/`.some (.uint n)` and a `size` observes `.nat n`, so `encodeArrayRead` is
injective and every primitive observation is detached from every root. This is
the *logical* witness that the class's laws are inhabited; it is not a proof that
a compiled `set` updates in place. That is the run-time harness's job
(`ScidoniaInPlace`), and the negative control in the check library shows that the
laws are not vacuous.

Array bounds, size preservation and "`false` exactly when out of bounds" are
instance-specific lemmas here (`arrayReplace_size`, `arrayReplace_bounds`), not
class laws: a different state variable replaces unconditionally.
-/
import Scidonia.FracPerm.StateVar.Heap
import Scidonia.FracPerm.Structured.Model
import Scidonia.FracPerm.Structured.Executor

namespace Scidonia.FracPerm.StateVar

/-- A read operation of the array: observe one element, or the size. -/
inductive ArrayReadOp where
  /-- Observe the element at `i`, or nothing when `i` is out of bounds. -/
  | get (i : Nat)
  /-- Observe the array's size. -/
  | size
deriving DecidableEq, Repr

/-- A write operation of the array: put `v` at `i`. -/
abbrev ArrayWriteOp := Nat × UInt64

/-- What an array read operation yields. -/
def ArrayResult : ArrayReadOp → Type
  | .get _ => Option UInt64
  | .size => Nat

/-- Observe an array read operation, as the structured interface's `Reader.get`
and `Reader.size` do: `a[i]?` for a `get`, `a.size` for a `size`. -/
def arrayObserve (o : ArrayReadOp) (a : Array UInt64) : ArrayResult o :=
  match o with
  | .get i => a[i]?
  | .size => a.size

/-- Replace an array by a write, as the structured interface's `Program.set`
does: `v` goes in at `i` when the index is in bounds and `true` is reported, and
an out-of-bounds index leaves the array alone and reports `false`. -/
def arrayReplace (w : ArrayWriteOp) (a : Array UInt64) : Array UInt64 × Bool :=
  if w.1 < a.size then (a.set! w.1 w.2, true) else (a, false)

/-- Encode an array read result: a `get` observes `.none` or `.some (.uint n)`,
a `size` observes `.nat n`. The encoding is constructor-faithful — no two
distinct results encode alike, and an element value is a word, not a location. -/
def encodeArrayRead : (o : ArrayReadOp) → ArrayResult o → Value
  | .get _, none => .none
  | .get _, some x => .some (.uint x)
  | .size, n => .nat n

/-- An array observation is detached from every root: `encodeArrayRead` never
produces a `.loc`. -/
theorem arrayObserve_detached (ℓ : Loc) (o : ArrayReadOp) (a : Array UInt64) :
    NoRef ℓ (encodeArrayRead o (arrayObserve o a)) := by
  cases o with
  | get i =>
    cases h : a[i]? with
    | none => simp [encodeArrayRead, arrayObserve, h, NoRef]
    | some v => simp [encodeArrayRead, arrayObserve, h, NoRef]
  | size => simp [encodeArrayRead, arrayObserve, NoRef]

/-- `encodeArrayRead` distinguishes results: two results an operation encodes as
the same value are the same result. -/
theorem encodeArrayRead_injective (o : ArrayReadOp) (x y : ArrayResult o) :
    encodeArrayRead o x = encodeArrayRead o y → x = y := by
  intro h
  cases o with
  | get i =>
    simp only [encodeArrayRead] at h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some _ => nomatch h
    | some a =>
      cases y with
      | none => nomatch h
      | some b => exact congrArg some (Value.uint.inj (Value.some.inj h))
  | size =>
    simp only [encodeArrayRead] at h
    exact Value.nat.inj h

/-- An array write preserves the array's size: an out-of-bounds index leaves the
array alone, and an in-bounds one replaces an element. This is an
instance-specific lemma, not a class law. -/
theorem arrayReplace_size (a : Array UInt64) (w : ArrayWriteOp) :
    (arrayReplace w a).1.size = a.size := by
  by_cases h : w.1 < a.size <;> simp [arrayReplace, h]

/-- An array write reports `true` exactly when the index was in bounds; an
out-of-bounds write leaves the array alone. Instance-specific, as
`arrayReplace_size`. -/
theorem arrayReplace_bounds (a : Array UInt64) (w : ArrayWriteOp) :
    (arrayReplace w a).2 = true ↔ w.1 < a.size := by
  by_cases h : w.1 < a.size <;> simp [arrayReplace, h]

/-- The array as a lawful state variable.

A state is an `Array UInt64`; `Structured.Init` is what a fresh one is created
from, exactly as `Executor.runFresh` creates it, so the runner's array and this
instance's `initial` agree. Every array state is `Valid` — this instance has no
inadmissible arrays — and the class's four laws are the lemmas above. -/
instance arrayStateVar : LawfulStateVar (Array UInt64) Scidonia.FracPerm.Structured.Init
    ArrayReadOp ArrayWriteOp where
  Result := ArrayResult
  initial init := Array.replicate init.size init.fill
  Valid _ := True
  observe := arrayObserve
  replace := arrayReplace
  encodeRead := encodeArrayRead
  initial_valid _ := trivial
  replace_valid _ _ _ := trivial
  encodeRead_injective := encodeArrayRead_injective
  observe_detached := fun ℓ o a _ => arrayObserve_detached ℓ o a

/-- Translate the structured interface's read tree into the generic read recipe:
a `get` becomes a read of the corresponding operation, a `size` a read of the
size operation, and continuations are translated recursively. -/
def liftR : Scidonia.FracPerm.Structured.RTree α →
    RTree ArrayReadOp ArrayResult α
  | .pure a => .pure a
  | .get i k => .read (.get i) (fun o => liftR (k o))
  | .size k => .read .size (fun n => liftR (k n))
  | .fork l r k => .fork (liftR l) (liftR r) (fun p => liftR (k p))

/-- Translate the structured interface's program tree into the generic program
recipe; as `liftR`, with `set i v` becoming the write `(i, v)` and a read phase's
tree translated by `liftR`. -/
def liftP : Scidonia.FracPerm.Structured.PTree α →
    PTree ArrayReadOp ArrayResult ArrayWriteOp α
  | .pure a => .pure a
  | .set i v k => .write (i, v) (fun b => liftP (k b))
  | .phase r k => .phase (liftR r) (fun a => liftP (k a))

/-- The generic denotation of a translated read tree is the structured
denotation of the tree: the translation preserves the values a read tree
computes. -/
theorem bridge_val (s : Array UInt64) (t : Scidonia.FracPerm.Structured.RTree α) :
    val s (liftR t) = Scidonia.FracPerm.Structured.val s t := by
  induction t generalizing s with
  | pure a => rfl
  | get i k ih =>
    show (run s (liftR (k s[i]?))).1 = (Scidonia.FracPerm.Structured.run s (k s[i]?)).1
    exact ih (s := s) s[i]?
  | size k ih =>
    show (run s (liftR (k s.size))).1 =
      (Scidonia.FracPerm.Structured.run s (k s.size)).1
    exact ih (s := s) s.size
  | fork l r k ihl ihr ihk =>
    show (run s (liftR (k ((run s (liftR l)).1, (run s (liftR r)).1)))).1 =
      (Scidonia.FracPerm.Structured.run s
        (k ((Scidonia.FracPerm.Structured.run s l).1,
          (Scidonia.FracPerm.Structured.run s r).1))).1
    have hl : (run s (liftR l)).1 = (Scidonia.FracPerm.Structured.run s l).1 :=
      ihl (s := s)
    have hr : (run s (liftR r)).1 = (Scidonia.FracPerm.Structured.run s r).1 :=
      ihr (s := s)
    rw [hl, hr]
    exact ihk (s := s) _
/-
The `show` in each case is the two denotations' unfoldings, which are equal by
definition; the fork case's `hl`/`hr` rewrite the branch results the generic fork
computes to the structured ones. -/

/-- The generic denotation of a translated program tree is the structured
denotation of the tree. -/
theorem bridge_pval (s : Array UInt64) (t : Scidonia.FracPerm.Structured.PTree α) :
    pval s (liftP t) = Scidonia.FracPerm.Structured.pval s t := by
  induction t generalizing s with
  | pure a => rfl
  | set i v k ih =>
    by_cases h : i < s.size
    · simp only [liftP, pval, Scidonia.FracPerm.Structured.pval, LawfulStateVar.replace,
        arrayReplace, ite_eq_left h]
      exact ih (s := s.set! i v) true
    · simp only [liftP, pval, Scidonia.FracPerm.Structured.pval, LawfulStateVar.replace,
        arrayReplace, ite_eq_right h]
      exact ih (s := s) false
  | phase r k ih =>
    simp only [liftP, pval, Scidonia.FracPerm.Structured.pval]
    rw [bridge_val s r]
    exact ih (s := s) (Scidonia.FracPerm.Structured.val s r)

/-- The shipped runner against the generic denotation: `runFresh` creates the
array this instance's `initial` describes, and the generic denotation of the
translated tree is what the structured denotation computes — so the array's
existing public behaviour is the generic model at this instance, without a second
runner. -/
theorem runFresh_eq_pval (init : Scidonia.FracPerm.Structured.Init)
    (p : Scidonia.FracPerm.Structured.Program α) :
    Scidonia.FracPerm.Structured.runFresh init p = (do
      let a : Array UInt64 := LawfulStateVar.initial init
      return pval a (liftP (Scidonia.FracPerm.Structured.Program.treeOf p))) := by
  rw [Scidonia.FracPerm.Structured.runFresh_eq_pval]
  have hinit : LawfulStateVar.initial init = Array.replicate init.size init.fill := rfl
  rw [hinit]
  simp only [bridge_pval]

end Scidonia.FracPerm.StateVar
