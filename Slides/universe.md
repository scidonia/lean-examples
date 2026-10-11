# Models 3 and 4: lawful by description

## Three ways to establish lawfulness
- **Prove it directly**, as for the buffer and the `UInt64` array: give `Valid`, then discharge the four laws by cases on the operations.
- **Transport it along an isomorphism**, as for `Slot`: prove the laws once for a description, then carry each one across `encode`/`decode` using the two inverse laws. The type itself needs no law proof.
- **Get it by construction**, as for the sealed class: name a layout and prove the type *is* its state type. The library defines the operations and derives all four laws.
- Each step down moves work from the instance author into the library. The models that follow are the second and third.

## Model 3: a description universe
- *The Gentle Art of Levitation* (Chapman, Dagand, McBride, Morris): describe datatypes by a type of descriptions, and interpret each one.
- Ours is small and non-recursive: `unit`, `nat`, `sum`.
- `Slot` is a real Lean inductive; `slotDesc` describes it, and `encode`/`decode` are inverse in ==both== directions.

```slot, described
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar

example : El slotDesc = (Unit ⊕ Nat) := rfl

example (s : Slot) : decode (encode s) = s := decode_encode s
example (r : El slotDesc) : encode (decode r) = r := encode_decode r

example : encode (Slot.full 7) = Sum.inr 7 := rfl
```

## Slot as a state variable
- The laws are proved for the description and carried to `Slot` across the isomorphism — none is proved for `Slot` itself.
- Reading after a write returns the written value.
- A snapshot survives: `full 7` read before a write stays `full 7`; the cell then holds `full 9`.
- One cell changes shape: `empty → full n → empty`.

```snapshot
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar

example (s t : Slot) :
    LawfulStateVar.observe () (LawfulStateVar.replace t s).1 = t :=
  slot_read_after_replace s t

example (n : Nat) {ℓ : Loc} {h₀ h₁ h₂ : Heap Slot} {b c : Bool}
    (h0 : At ℓ Slot.empty h₀)
    (hw1 : WriteAt slotStateVar ℓ (Slot.full n) h₀ h₁ b)
    (hw2 : WriteAt slotStateVar ℓ Slot.empty h₁ h₂ c) :
    At ℓ (Slot.full n) h₁ ∧ At ℓ Slot.empty h₂ :=
  let r := slot_shape_change n h0 hw1 hw2
  ⟨r.2.2.1, r.2.2.2.1⟩
```

## Model 4: every description at once
- `encodeEl d` encodes any element of any description — injective and reference-free, by induction on `d`.
- `describedStateVar d`: ==one instance for every description==, its four laws proved once.
- `transport`: any type isomorphic to some `El d` is a lawful state variable.

```one instance for all
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar

example (d : Desc) :
    LawfulStateVar (Described d) (El d) Unit (El d) :=
  describedStateVar d

example (d : Desc) (s : Described d) (x : El d) :
    (describedStateVar d).observe ()
      ((describedStateVar d).replace x s).1 = x :=
  universe_read_after_replace d s x
```

## Slot by transport
- `Slot`'s instance is now one line: transport along its isomorphism.
- Model 3's description-specific proofs are deleted; every public `Slot` theorem keeps its statement.
- A second datatype costs only its isomorphism — `Bool` at `sum unit unit` is checked the same way.

```slot, one line
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar

-- the whole instance:
example : LawfulStateVar Slot Slot Unit Slot :=
  transport slotDesc Slot encode decode decode_encode encode_decode
```
