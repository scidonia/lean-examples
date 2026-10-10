/-
One lawful state variable for every description, and the transport that carries
it to any type isomorphic to a description's element type.

`Desc` (`Scidonia.FracPerm.StateVar.Description`) describes a type as a unit, a
natural, or a sum of two descriptions. This module encodes an element of *any*
description as a logical value:

* `encodeEl d x` sends a unit to `.unit`, a natural to `.nat n`, and a sum to
  the tagged encoding of the summand that was chosen.
* `encodeEl_injective` and `encodeEl_noRef` are the two facts a lawful instance
  needs, and each is proved *once*, by a structural induction on `d` with one
  case per constructor of `Desc`, rather than once per description. The first
  says the encoding distinguishes elements of the same description; the second
  says it never names a root.

The wrapper `Described d` holds an element of `El d`. It exists because
typeclass inference is indexed by the description: two descriptions can denote
definitionally equal Lean types, so an instance stated on `El d` itself could
not be found from a state's type. With the wrapper, the single instance

    describedStateVar d : LawfulStateVar (Described d) (El d) Unit (El d)

serves every description. A state is a wrapper around a described element, a
read returns the wrapped element, a write installs an element, and the encoding
is `encodeEl d`. Its four law fields are the two lemmas above together with the
triviality of `True` validity — there is no per-description proof.

The generic theorems of `Scidonia.FracPerm.StateVar.Model` and
`Scidonia.FracPerm.StateVar.Heap` then apply at `describedStateVar d` for an
arbitrary `d`. `universe_read_after_replace`, `universe_read_detached`,
`universe_read_at_detached`, `universe_write_at_valid`, `universe_write_at_frame`
and `universe_snapshot_after_write` are those applications, not new proofs; each
is stated so that a client of an unspecified description can use it.

`transport` carries the instance to any type `τ` with an isomorphism to `El d`:
a `toEl : τ → El d`, an `ofEl : El d → τ`, and the two inverse laws. Its
operations are the universe instance's conjugated by the isomorphism, and each
of its law fields is the corresponding universe law after an inverse law cancels
the conjugation — never a fresh proof. `Scidonia.FracPerm.StateVar.Slot`
obtains a slot's instance from `transport` at `slotDesc`, and the checks in
`ScidoniaTest/Universe.lean` obtain a second, independent one for `Bool` at
`sum unit unit`, so the transport is not specific to the slot.

Scope. This is the same logical encoding as `Value` and the same logical heap as
the rest of the generic interface. `encodeEl` is an *encoding*, and
`encodeEl_noRef` is a proposition about it — it is not a theorem about Lean's
object graph, reference counting or foreign pointers, and an encoding that
declined to represent a real run-time pointer as `.loc` would not be caught by
it. A write produces a new wrapper, or a new heap value over wrappers, and
destroys nothing. The description universe is deliberately non-recursive, so
every proof here is a finite case analysis; nothing is claimed about recursive
inductives, about arbitrary Lean types, or about descriptions of types other
than unit, natural and sum.
-/
import Scidonia.FracPerm.StateVar.Description
import Scidonia.FracPerm.StateVar.Heap

namespace Scidonia.FracPerm.StateVar

/-! ## Encoding an element of any description

One case per constructor of `Desc`. The encoding of a sum is the tagged encoding
of the summand that was chosen, so the `.inl`/`.inr` tags of `Value` carry the
description's own sum structure. -/

/-- Encode an element of a description as a logical value: a unit as `.unit`, a
natural as `.nat n`, and a sum as the tagged encoding of its summand. -/
def encodeEl : (d : Desc) → El d → Value
  | .unit, _ => .unit
  | .nat, n => .nat n
  | .sum a _, Sum.inl x => .inl (encodeEl a x)
  | .sum _ b, Sum.inr y => .inr (encodeEl b y)

/-- `encodeEl` distinguishes elements of one description: two elements it
encodes as the same value are the same element. The proof is a structural
induction on the description, one case per constructor of `Desc` — the unit case
collapses because `Unit` has one element, the natural case is injectivity of
`Value.nat`, and a sum case is the tags' discrimination together with the
chosen summand's injectivity.

Injectivity is stated at a *fixed* description because elements of different
descriptions live in different types: `x : El a` and `y : El b` with `a ≠ b` are
not two observations of one state variable, and there is no equation between
`encodeEl a x` and `encodeEl b y` to prove or refute. -/
theorem encodeEl_injective : ∀ (d : Desc) (x y : El d),
    encodeEl d x = encodeEl d y → x = y
  | .unit, x, y, _ => by cases x; cases y; rfl
  | .nat, x, y, h => Value.nat.inj h
  | .sum a _, Sum.inl x, Sum.inl y, h => by
      have h' : encodeEl a x = encodeEl a y := Value.inl.inj h
      rw [encodeEl_injective a x y h']
  | .sum _ _, Sum.inl _, Sum.inr _, h => absurd h (by simp [encodeEl])
  | .sum _ _, Sum.inr _, Sum.inl _, h => absurd h (by simp [encodeEl])
  | .sum _ b, Sum.inr x, Sum.inr y, h => by
      have h' : encodeEl b x = encodeEl b y := Value.inr.inj h
      rw [encodeEl_injective b x y h']

/-- An element of any description is detached from every root: the encoding of a
unit, a natural or a sum names no `.loc`. The proof is a structural induction on
the description, one case per constructor, with the sum cases descending into
the summand that was chosen. -/
theorem encodeEl_noRef (ℓ : Loc) : ∀ (d : Desc) (x : El d), NoRef ℓ (encodeEl d x)
  | .unit, x => by cases x; trivial
  | .nat, _ => trivial
  | .sum a _, Sum.inl x => encodeEl_noRef ℓ a x
  | .sum _ b, Sum.inr y => encodeEl_noRef ℓ b y

/-! ## One instance for every description -/

/-- An element of `El d`, wrapped so that typeclass inference is indexed by the
description `d` itself. Two descriptions can denote definitionally equal Lean
types, so a state variable stated on `El d` would leave the description to be
guessed; the wrapper makes `d` an explicit index of the state type. -/
structure Described (d : Desc) where
  /-- The described element. -/
  value : El d

/-- Every description is a lawful state variable. The state is a wrapper around
a described element, initialized from an element; a read returns the element, a
write installs one unconditionally, and the encoding is `encodeEl`.

The four law fields are `encodeEl_injective` and `encodeEl_noRef` together with
the triviality of `True` validity — one proof, at an arbitrary description. -/
instance describedStateVar (d : Desc) :
    LawfulStateVar (Described d) (El d) Unit (El d) where
  Result _ := El d
  initial x := ⟨x⟩
  Valid _ := True
  observe _ s := s.value
  replace x _ := (⟨x⟩, true)
  encodeRead _ x := encodeEl d x
  initial_valid _ := trivial
  replace_valid _ _ _ := trivial
  encodeRead_injective _ := encodeEl_injective d
  observe_detached ℓ _ s _ := encodeEl_noRef ℓ d s.value

/-- A read of the universe instance returns the wrapped element. -/
theorem universe_observe_eq (d : Desc) (s : Described d) :
    (describedStateVar d).observe () s = s.value := rfl

/-- A write of the universe instance installs the element and reports `true`:
there is no bound to fail at a single root cell. -/
theorem universe_replace_eq (d : Desc) (x : El d) (s : Described d) :
    (describedStateVar d).replace x s = (⟨x⟩, true) := rfl

/-- The universe instance's encoding of a read result is `encodeEl`. -/
theorem universe_encodeRead_eq (d : Desc) (x : El d) :
    (describedStateVar d).encodeRead () x = encodeEl d x := rfl

/-- Reading after replacing yields the replacement, at an arbitrary
description. -/
theorem universe_read_after_replace (d : Desc) (s : Described d) (x : El d) :
    (describedStateVar d).observe () ((describedStateVar d).replace x s).1 = x := by
  rw [universe_replace_eq, universe_observe_eq]

/-- A read of an arbitrary description is detached from every root: the encoded
observation names no `.loc`. -/
theorem universe_read_detached (d : Desc) (ℓ : Loc) (s : Described d) :
    NoRef ℓ (encodeEl d ((describedStateVar d).observe () s)) :=
  encodeEl_noRef ℓ d ((describedStateVar d).observe () s)

/-! ## The generic model at an arbitrary description

Each theorem below is the corresponding theorem of
`Scidonia.FracPerm.StateVar.Heap` applied at `describedStateVar d`; none is
re-proved. They are what a client of an unspecified description uses. -/

/-- What a read of a heap cell holding an element of an arbitrary description
returns is detached from the root it read. -/
theorem universe_read_at_detached (d : Desc) {ℓ : Loc} {h h' : Heap (Described d)}
    {v : El d} (hr : ReadAt (describedStateVar d) ℓ () h h' v) :
    NoRef ℓ (encodeEl d v) :=
  read_at_detached hr

/-- A write of an arbitrary description leaves the cell holding an admissible
state. -/
theorem universe_write_at_valid (d : Desc) {ℓ : Loc} {x : El d}
    {h h' : Heap (Described d)} {b : Bool}
    (hw : WriteAt (describedStateVar d) ℓ x h h' b) :
    ∃ s', At ℓ s' h' ∧ (describedStateVar d).Valid s' :=
  write_at_valid hw

/-- A write of an arbitrary description changes no cell other than its root. -/
theorem universe_write_at_frame (d : Desc) {ℓ m : Loc} {x : El d}
    {h h' : Heap (Described d)} {b : Bool}
    (hw : WriteAt (describedStateVar d) ℓ x h h' b) (hm : m ≠ ℓ) : h' m = h m :=
  write_at_frame hw hm

/-- The read–write–read snapshot at an arbitrary description: the first read's
value is bound to the *pre-write* cell and the second read's to the *post-write*
cell. This is the generic `snapshot_after_write` at `describedStateVar d`. -/
theorem universe_snapshot_after_write (d : Desc) {ℓ : Loc} {x : El d}
    {h h' : Heap (Described d)} {b : Bool} {v v' : El d}
    (hr : ReadAt (describedStateVar d) ℓ () h h v)
    (hw : WriteAt (describedStateVar d) ℓ x h h' b)
    (hr' : ReadAt (describedStateVar d) ℓ () h' h' v') :
    ∃ s, At ℓ s h ∧ v = (describedStateVar d).observe () s ∧
      v' = (describedStateVar d).observe () ((describedStateVar d).replace x s).1 :=
  snapshot_after_write hr hw hr'

/-! ## Transport along an isomorphism

Any type with an isomorphism to a description's element type is a lawful state
variable: the operations are the universe instance's conjugated by the
isomorphism, so the state, the initialization input and the write input are all
the transported type. Every law field is the universe instance's law after the
inverse law that cancels the conjugation. -/

/-- The universe instance's operations carried along an isomorphism
`τ ≃ El d` given by `toEl`/`ofEl` and the two inverse laws. The transported
instance is *not* a fresh witness: each field is the universe instance's
operation conjugated by the isomorphism.

The definition is a value of the class's type rather than a typeclass instance,
since its arguments cannot be found by instance search, so it is marked
`instance_reducible` for the same reason an instance is. -/
@[instance_reducible]
def transport (d : Desc) (τ : Type) (toEl : τ → El d) (ofEl : El d → τ)
    (ofEl_toEl : ∀ x, ofEl (toEl x) = x) (toEl_ofEl : ∀ y, toEl (ofEl y) = y) :
    LawfulStateVar τ τ Unit τ where
  Result _ := τ
  initial s := ofEl (toEl s)
  Valid _ := True
  observe _ s := ofEl (toEl s)
  replace x s := (ofEl (toEl x), true)
  encodeRead _ s := encodeEl d (toEl s)
  initial_valid _ := trivial
  replace_valid _ _ _ := trivial
  encodeRead_injective _ x y h := by
    have h' : toEl x = toEl y := encodeEl_injective d (toEl x) (toEl y) h
    calc x = ofEl (toEl x) := (ofEl_toEl x).symm
      _ = ofEl (toEl y) := by rw [h']
      _ = y := ofEl_toEl y
  observe_detached ℓ _ s _ := by
    show NoRef ℓ (encodeEl d (toEl (ofEl (toEl s))))
    rw [toEl_ofEl]
    exact encodeEl_noRef ℓ d (toEl s)

/-- A transported state is initialized to itself: the isomorphism cancels. -/
theorem transport_initial_self (d : Desc) (τ : Type) (toEl : τ → El d)
    (ofEl : El d → τ) (ofEl_toEl : ∀ x, ofEl (toEl x) = x)
    (toEl_ofEl : ∀ y, toEl (ofEl y) = y) (s : τ) :
    (transport d τ toEl ofEl ofEl_toEl toEl_ofEl).initial s = s :=
  ofEl_toEl s

/-- A transported read returns the state: the isomorphism cancels. -/
theorem transport_observe_self (d : Desc) (τ : Type) (toEl : τ → El d)
    (ofEl : El d → τ) (ofEl_toEl : ∀ x, ofEl (toEl x) = x)
    (toEl_ofEl : ∀ y, toEl (ofEl y) = y) (s : τ) :
    (transport d τ toEl ofEl ofEl_toEl toEl_ofEl).observe () s = s :=
  ofEl_toEl s

/-- A transported write installs its operand and reports `true`. -/
theorem transport_replace_self (d : Desc) (τ : Type) (toEl : τ → El d)
    (ofEl : El d → τ) (ofEl_toEl : ∀ x, ofEl (toEl x) = x)
    (toEl_ofEl : ∀ y, toEl (ofEl y) = y) (x s : τ) :
    (transport d τ toEl ofEl ofEl_toEl toEl_ofEl).replace x s = (x, true) :=
  Prod.ext (ofEl_toEl x) rfl

/-- A transported read is encoded by `encodeEl` of the element the state names:
this is the transported encoding's definition. -/
theorem transport_encodeRead_eq (d : Desc) (τ : Type) (toEl : τ → El d)
    (ofEl : El d → τ) (ofEl_toEl : ∀ x, ofEl (toEl x) = x)
    (toEl_ofEl : ∀ y, toEl (ofEl y) = y) (s : τ) :
    (transport d τ toEl ofEl ofEl_toEl toEl_ofEl).encodeRead () s =
      encodeEl d (toEl s) := rfl

/-- Reading after replacing yields the replacement, for any transported type.
Both inverse laws are used: the write's result is re-observed by the
isomorphism, and cancelling the round trip is what makes the read the
replacement. -/
theorem transport_read_after_replace (d : Desc) (τ : Type) (toEl : τ → El d)
    (ofEl : El d → τ) (ofEl_toEl : ∀ x, ofEl (toEl x) = x)
    (toEl_ofEl : ∀ y, toEl (ofEl y) = y) (s t : τ) :
    (transport d τ toEl ofEl ofEl_toEl toEl_ofEl).observe ()
      ((transport d τ toEl ofEl ofEl_toEl toEl_ofEl).replace t s).1 = t := by
  show ofEl (toEl (ofEl (toEl t))) = t
  rw [toEl_ofEl (toEl t), ofEl_toEl t]

end Scidonia.FracPerm.StateVar
