import Scidonia.FracPerm

open Scidonia.FracPerm.StateVar

/-! A fixed-capacity buffer of four words: a read is an index or the size, a
write replaces one in-bounds word, and the invariant is that the buffer keeps
exactly four words. -/

inductive BufRead where
  | get (i : Nat)
  | size

abbrev BufResult : BufRead → Type
  | .get _ => Option UInt64
  | .size => Nat

def bufObserve : (o : BufRead) → Array UInt64 → BufResult o
  | .get i, a => a[i]?
  | .size, a => a.size

def bufReplace (w : Nat × UInt64) (a : Array UInt64) : Array UInt64 × Bool :=
  if w.1 < a.size then (a.set! w.1 w.2, true) else (a, false)

def bufEncode : (o : BufRead) → BufResult o → Value
  | .get _, none => .none
  | .get _, some v => .some (.uint v)
  | .size, n => .nat n

def BufValid (a : Array UInt64) : Prop := a.size = 4

theorem buf_initial_valid (v : UInt64) : BufValid (Array.replicate 4 v) := by
  -- slide-step
  unfold BufValid
  -- slide-step
  simp

theorem buf_replace_valid (w : Nat × UInt64) (a : Array UInt64) (h : BufValid a) :
    BufValid (bufReplace w a).1 := by
  -- slide-step
  unfold BufValid bufReplace at *
  -- slide-step
  split
  -- slide-step
  case isTrue => simp [h]
  -- slide-step
  case isFalse => exact h

theorem buf_encode_injective (o : BufRead) (x y : BufResult o)
    (h : bufEncode o x = bufEncode o y) : x = y := by
  -- slide-step
  cases o
  -- slide-step
  case get i => cases x <;> cases y <;> simp_all [bufEncode]
  -- slide-step
  case size => simpa [bufEncode] using h

theorem buf_detached (ℓ : Loc) (o : BufRead) (a : Array UInt64) :
    NoRef ℓ (bufEncode o (bufObserve o a)) := by
  -- slide-step
  cases o
  -- slide-step
  case get i => simp only [bufObserve]; cases a[i]? <;> simp [bufEncode, NoRef]
  -- slide-step
  case size => simp [bufObserve, bufEncode, NoRef]

@[instance_reducible] def bufStateVar :
    LawfulStateVar (Array UInt64) UInt64 BufRead (Nat × UInt64) where
  Result := BufResult
  initial v := Array.replicate 4 v
  Valid := BufValid
  observe := bufObserve
  replace := bufReplace
  encodeRead := bufEncode
  initial_valid := buf_initial_valid
  replace_valid := buf_replace_valid
  encodeRead_injective := buf_encode_injective
  observe_detached ℓ o a _ := buf_detached ℓ o a
