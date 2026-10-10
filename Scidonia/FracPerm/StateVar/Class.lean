/-
The lawful state-variable class: what a state variable must prove about itself
to be used by the generic structured model.

`Scidonia.FracPerm.FracObject` (`Scidonia/FracPerm/Hoare.lean`) states the
interface's *rules* in prose, because they are about how Lean's values are
represented at run time and cannot be checkable from specifications: a read
must not hand back a mutable part of the state, and an update must not keep an
old part alive. `LawfulStateVar` is a class in which the logical part of those
obligations is an actual proof field, over a chosen *observation encoding*
(`Scidonia.FracPerm.StateVar.Value`).

The laws, and exactly what each one scopes over:

* `initial_valid` — a state built from an initializer is admissible. It says
  nothing about fresh machine allocation or run-time uniqueness.
* `replace_valid` — exclusive logical replacement closes admissible states.
  It does not say the old Lean object was destroyed or that retained references
  were dropped; it is a statement about the modeled state.
* `encodeRead_injective` — the encoding distinguishes observation values, so a
  constant encoding such as "always `.unit`" cannot certify two distinct read
  results as the same. It is injectivity of the encoding, not physical
  representation identity.
* `observe_detached` — for every `ℓ`, a primitive observation of a valid state
  encodes without a reference to `ℓ`, including beneath `some`, `inl`, `inr`
  and `pair`. It refuses a modeled `.loc ℓ`; it does not establish that an
  arbitrary client continuation, a closure with an externally supplied state, or
  a compiled primitive implementation contains no physical alias.

`observe` is a pure function, so read-only store behavior is obtained by
construction of the transition (`Scidonia.FracPerm.StateVar.Heap`), not by an
independent axiom. `replace` returns `σ × Bool` to match the structured
interface's `Program.set : Program Bool`, whose `Bool` is whether the write was
in bounds; array bounds, size preservation and failure-on-out-of-bounds are
instance-specific lemmas, not universal class laws, because a different state
variable (a slot, say) replaces unconditionally.

The class has no effectful or unchecked operation, and no share argument: no
client value on the runtime path names a fraction.

Membership is by proof, not by inheritance: an existing `FracObject` instance
is **not** automatically a `LawfulStateVar`, and none of the historical
instances is claimed as one. `Scidonia.FracPerm.StateVar.Array` gives the
array's witness; the negative controls in the check library show that the laws
are not vacuous.
-/
import Scidonia.FracPerm.StateVar.Value

namespace Scidonia.FracPerm.StateVar

/-- A lawful state variable: a state type, what it is initialized from, its
read and write operation types, how a read result is encoded as a `Value`, and
the four laws a client of the generic structured model may rely on.

`Init`, `ReadOp` and `WriteOp` are `outParam`s, following
`Scidonia.FracPerm.FracObject`: the state type `σ` alone must determine them, so
that an argument whose expected type is written from the instance's operation
types can be elaborated from the instance alone. -/
class LawfulStateVar (σ : Type) (Init : outParam Type)
    (ReadOp : outParam Type) (WriteOp : outParam Type) where
  /-- The value a read operation yields. A read operation may yield a value of
  any type, one per operation, as `FracObject.Result` does. -/
  Result : ReadOp → Type
  /-- A state built from an initializer. -/
  initial : Init → σ
  /-- The admissible states of the variable. -/
  Valid : σ → Prop
  /-- Perform a read operation. It is a pure function of the operation and the
  state. -/
  observe : (o : ReadOp) → σ → Result o
  /-- Replace the state by an exclusive logical replacement, and report whether
  the write took effect (`false` for a write that the variable declined, as an
  out-of-bounds array write is). -/
  replace : WriteOp → σ → σ × Bool
  /-- Encode a read result as a logical value. -/
  encodeRead : (o : ReadOp) → Result o → Value
  /-- `initial` builds admissible states: fresh construction is admissible. -/
  initial_valid : ∀ i : Init, Valid (initial i)
  /-- `replace` closes admissible states: an exclusive logical replacement of an
  admissible state is admissible. -/
  replace_valid : ∀ (w : WriteOp) (s : σ),
    Valid s → Valid (replace w s).1
  /-- `encodeRead` distinguishes read results: two results an operation encodes
  as the same value are the same result. -/
  encodeRead_injective : ∀ (o : ReadOp) (x y : Result o),
    encodeRead o x = encodeRead o y → x = y
  /-- A primitive observation of a valid state is detached from every root: its
  encoding names no `.loc ℓ`, for every `ℓ`, beneath any compound
  observation. -/
  observe_detached : ∀ (ℓ : Loc) (o : ReadOp) (s : σ),
    Valid s → NoRef ℓ (encodeRead o (observe o s))

end Scidonia.FracPerm.StateVar
