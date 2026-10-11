/-
A *sealed* state variable: a type whose states are, up to one equality, the
states of a layout, with no code of its own.

`Scidonia.FracPerm.StateVar.Class`'s `LawfulStateVar` asks an instance author for
an observation operation and an encoding, so the laws can only constrain what the
author chose to supply: the class accepts an instance whose read names the state
itself (`ScidoniaTest/Model5.lean`'s countermodel is one). Model 5's adapter
closes that route for layout states, but an author who wants to use it must adopt
the library's `DescribedLayout` wrapper.

`SealedStateVar` is the same idea as an interface rather than a wrapper. An
instance supplies exactly two things: the layout its type is, and the proof that
the type *is* that layout's state type. It supplies no read, no write and no
encoding. The library defines those once, through `rep`:

* `read? p : σ → Option Value` is `Layout5.read?` at the layout, after the cast;
* `setLeaf p x : σ → σ × Bool` is `Layout5.setLeaf` at the layout, through the
  cast in both directions.

and derives `sealedLawful [SealedStateVar σ]`, a `LawfulStateVar σ σ (ObsPath _)
(LayoutWrite _)` whose fields are Model 5's adapter transported along `rep`. Its
four laws are the adapter's, so they are proved by transport rather than per
instance: `encodeRead` is the library's encoding (`rfl`), `Result p` is
`Option (ObsEl p.obs)` (`rfl`), and both are unreachable from an instance — the
class has no field for either.

The guarantee is structural, not a proof about Lean's object graph: a sealed read
returns an `Option Value` built by `encodeObs`, which has no `.loc` branch, so it
cannot hand back a mutable part of the state. The write is the take-out update of
Model 5, and whether a compiled write updates in place is the run-time evidence
`ScidoniaInPlace` reports for the layout module; driving it through the sealed
class adds a cast, which erases (the instantiations below have `rep := rfl`) and
is checked for exactly that.

Scope limit. Only a type that is *definitionally* the layout's state type can be
sealed, because `rep : σ = State layout` must be an equality and the elaborator
must accept it. A user `structure` — say a pair of words declared as a struct —
would need an *isomorphism* to a layout's state instead, and an isomorphism is
not an equality: a write would have to convert between the two representations,
and whether that costs a copy has not been implemented or measured here. Arrays,
nested arrays, pairs and the observation universe's leaves are usable;
user-declared structures are not supported without a layout that names them.
-/
import Scidonia.FracPerm.StateVar.Layout5

namespace Scidonia.FracPerm.StateVar

open Layout5

/-- A sealed state variable: a type whose states are, up to `rep`, the states of
a layout. An instance supplies the layout and the equality; the library defines
the read, the write and the encoding from them, so an instance author cannot
choose any of the three. -/
class SealedStateVar (σ : Type) where
  /-- The layout whose state type `σ` is, up to `rep`. -/
  layout : Layout
  /-- `σ` is the layout's state type, up to this equality. -/
  rep : σ = State layout

namespace SealedStateVar

/-- The state cast into the layout's state type. -/
def toState {σ : Type} [SealedStateVar σ] (s : σ) :
    State (SealedStateVar.layout (σ := σ)) :=
  cast (SealedStateVar.rep (σ := σ)) s

/-- The library's read of a sealed state: the state transported to its layout by
`rep`, read by `Layout5.read?`. The result is an `Option Value` from the closed
observation universe, never a state or a subtree. -/
def read? {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) : σ → Option Value :=
  fun s => Layout5.read? p (toState s)

/-- The state cast back out of the layout's state type: the inverse of
`toState`. -/
def ofState {σ : Type} [SealedStateVar σ]
    (t : State (SealedStateVar.layout (σ := σ))) : σ :=
  cast (SealedStateVar.rep (σ := σ)).symm t

/-- The library's write of a sealed state: the new observation is installed by
`Layout5.setLeaf` at the layout, and the state it returns is cast back into `σ`.
The write's report is `Layout5.setLeaf`'s: `false` for a path that addresses
nothing, in which case the state is unchanged. -/
def setLeaf {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (x : ObsEl p.obs) : σ → σ × Bool :=
  fun s =>
    let r := Layout5.setLeaf p x (toState s)
    (ofState r.1, r.2)

/-- The derived lawful instance: Model 5's adapter, transported along `rep`. Its
read is `Layout5.read?`'s traversal on the layout state, its write is
`Layout5.setLeaf`'s, its encoding is the library's `encodeObs`, and its four laws
are the adapter's — so no sealed instance proves anything itself, and none can
supply an operation or an encoding that leaves the library's. -/
@[instance_reducible] def sealedLawful {σ : Type} [SealedStateVar σ] :
    LawfulStateVar σ σ (ObsPath (SealedStateVar.layout (σ := σ)))
      (LayoutWrite (SealedStateVar.layout (σ := σ))) where
  Result p := Option (ObsEl p.obs)
  initial i := i
  Valid _ := True
  observe p s :=
    (describedLayoutStateVar (SealedStateVar.layout (σ := σ))).observe p ⟨toState s⟩
  replace w s :=
    let r := (describedLayoutStateVar (SealedStateVar.layout (σ := σ))).replace w ⟨toState s⟩
    (ofState r.1.value, r.2)
  encodeRead p r := r.elim .none (fun x => .some (encodeObs p.obs x))
  initial_valid _ := trivial
  replace_valid _ _ _ := trivial
  encodeRead_injective p x y h :=
    (describedLayoutStateVar (SealedStateVar.layout (σ := σ))).encodeRead_injective p x y h
  observe_detached ℓ p s _ :=
    (describedLayoutStateVar (SealedStateVar.layout (σ := σ))).observe_detached ℓ p
      ⟨toState s⟩ trivial

/-! ## The structural statements

The two facts an instance has no say in. Both hold by `rfl`: the class declares no
field for either, so the derived instance's read result type and encoding are the
library's, and a client reads them off the definition rather than from a proof
about the instance. -/

/-- The derived instance's read result is the library's: an option of an element
of the closed observation universe, for every path. -/
theorem sealedLawful_Result {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) :
    (sealedLawful (σ := σ)).Result p = Option (ObsEl p.obs) := rfl

/-- The derived instance's encoding is the library's encoding: the adapter's, for
every path and read result. An instance cannot supply one — the class has no
field for it — so this is the only encoding a sealed instance has. -/
theorem sealedLawful_encodeRead {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (r : Option (ObsEl p.obs)) :
    (sealedLawful (σ := σ)).encodeRead p r =
      (describedLayoutStateVar (SealedStateVar.layout (σ := σ))).encodeRead p r := rfl

/-! ## Transporting along `rep`

The library's operations are the layout's operations through the cast in `rep`,
so the two directions of the round trip and the two projections of a write are
all the statements below need. -/

private theorem cast_cast {α β : Type} (h : α = β) (x : β) : cast h (cast h.symm x) = x := by
  cases h
  rfl

private theorem cast_cast_symm {α β : Type} (h : α = β) (x : α) : cast h.symm (cast h x) = x := by
  cases h
  rfl

/-- A layout state transported into `σ` and back is the state. -/
theorem toState_ofState {σ : Type} [SealedStateVar σ]
    (t : State (SealedStateVar.layout (σ := σ))) : toState (ofState (σ := σ) t) = t :=
  cast_cast (SealedStateVar.rep (σ := σ)) t

/-- A sealed state transported out and back is the state. -/
theorem ofState_toState {σ : Type} [SealedStateVar σ] (s : σ) :
    ofState (toState s) = s :=
  cast_cast_symm (SealedStateVar.rep (σ := σ)) s

/-- A sealed read is the layout read of the transported state. -/
@[simp] theorem read?_toState {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (s : σ) :
    read? p s = Layout5.read? p (toState s) := rfl

/-- A sealed write's state is the layout write's state, transported back. -/
theorem setLeaf_fst_toState {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (x : ObsEl p.obs) (s : σ) :
    toState (setLeaf p x s).1 = (Layout5.setLeaf p x (toState s)).1 :=
  toState_ofState _

/-- A sealed write's report is the layout write's report. -/
theorem setLeaf_snd {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (x : ObsEl p.obs) (s : σ) :
    (setLeaf p x s).2 = (Layout5.setLeaf p x (toState s)).2 := rfl

/-- The read at the path of a sealed state, written through the adapter: the
bridge the write theorems cross. -/
private theorem read?_eq_map_observe {d : Layout} (p : ObsPath d) (s : State d) :
    Layout5.read? p s =
      ((describedLayoutStateVar d).observe p ⟨s⟩).map (encodeObs p.obs) := rfl

/-! ## The theorems, for every sealed instance

Each is Model 5's theorem at the transported state: the sealed operations are the
layout's through `rep`, so nothing new is proved about a write, and an instance
inherits all four by being a `SealedStateVar`. -/

/-- Every sealed read result is detached from every root: it is the encoding of
an element of the observation universe, which names no `.loc`. -/
theorem sealedRead_detached {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (s : σ) (v : Value)
    (h : read? p s = some v) (ℓ : Loc) : NoRef ℓ v :=
  Layout5.read_detached p (toState s) v h ℓ

/-- A sealed write that took effect is read back as the observation that was
written: reading the path after the write returns the encoding of the write's
operand. -/
theorem sealedRead_after_setLeaf {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (x : ObsEl p.obs) (s : σ)
    (h : (setLeaf p x s).2 = true) :
    read? p (setLeaf p x s).1 = some (encodeObs p.obs x) := by
  have hw : (Layout5.setLeaf p x (toState s)).2 = true := (setLeaf_snd p x s).symm.trans h
  have hobs := Layout5.describedLayout_read_after_replace
    (SealedStateVar.layout (σ := σ)) p x ⟨toState s⟩ hw
  simp only [describedLayout_replace_eq] at hobs
  rw [read?_toState, setLeaf_fst_toState, read?_eq_map_observe, hobs]
  rfl

/-- The snapshot, at the sealed operations: a read taken before the write keeps
the value it read from the *old* state, while the read of the state the write
produced encodes the write's own operand. -/
theorem sealedSnapshot {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (s s' : σ) (old : Value)
    (new : ObsEl p.obs) (hread : read? p s = some old)
    (hwrite : setLeaf p new s = (s', true)) :
    read? p s = some old ∧ read? p s' = some (encodeObs p.obs new) := by
  have hs' : toState s' = (Layout5.setLeaf p new (toState s)).1 := by
    have h1 : (setLeaf p new s).1 = s' := congrArg Prod.fst hwrite
    rw [← h1]
    exact setLeaf_fst_toState p new s
  have hw : (Layout5.setLeaf p new (toState s)).2 = true :=
    (setLeaf_snd p new s).symm.trans (congrArg Prod.snd hwrite)
  have hwrite' : Layout5.setLeaf p new (toState s) = (toState s', true) :=
    Prod.ext hs'.symm hw
  refine ⟨hread, ?_⟩
  show Layout5.read? p (toState s') = some (encodeObs p.obs new)
  exact (Layout5.snapshot_after_setLeaf p (toState s) (toState s') old new hread hwrite').2

/-- A sealed write at a path disjoint from a read path does not change what that
read returns: `Disjoint` excludes the equal paths and every ancestor/descendant
pair, and the frame is a statement about the logical state, not about physical
ownership. -/
theorem sealedRead_frame {σ : Type} [SealedStateVar σ]
    (p q : ObsPath (SealedStateVar.layout (σ := σ))) (s s' : σ) (new : ObsEl p.obs)
    (hdisjoint : Disjoint p.path q.path) (hwrite : setLeaf p new s = (s', true)) :
    read? q s' = read? q s := by
  have hs' : toState s' = (Layout5.setLeaf p new (toState s)).1 := by
    have h1 : (setLeaf p new s).1 = s' := congrArg Prod.fst hwrite
    rw [← h1]
    exact setLeaf_fst_toState p new s
  have hw : (Layout5.setLeaf p new (toState s)).2 = true :=
    (setLeaf_snd p new s).symm.trans (congrArg Prod.snd hwrite)
  have hwrite' : Layout5.setLeaf p new (toState s) = (toState s', true) :=
    Prod.ext hs'.symm hw
  show Layout5.read? q (toState s') = Layout5.read? q (toState s)
  exact Layout5.read_frame p q (toState s) (toState s') new hdisjoint hwrite'

/-- A sealed write that reports failure leaves the state alone: the state is the
one the write was handed, not a rebuilt equal one. -/
theorem sealedSetLeaf_failed {σ : Type} [SealedStateVar σ]
    (p : ObsPath (SealedStateVar.layout (σ := σ))) (x : ObsEl p.obs) (s : σ)
    (h : (setLeaf p x s).2 = false) : (setLeaf p x s).1 = s := by
  have hw : (Layout5.setLeaf p x (toState s)).2 = false := (setLeaf_snd p x s).symm.trans h
  show ofState (Layout5.setLeaf p x (toState s)).1 = s
  rw [Layout5.setLeaf_failed p x (toState s) hw, ofState_toState]

/-! ## Instances

Two: an array of binary structs of machine words, whose `rep` is `rfl` because the
layout's state type *is* the array type, and a nested array of arrays of words.
Neither supplies a read or an encoding — the class has no field to put one in. -/

/-- The layout of the sealed array-of-structs instance: an array of binary
structs, each a pair of machine words. -/
abbrev sealedPairs : Layout := .arr (.struct (.leaf .uint) (.leaf .uint))

/-- An array of binary structs of machine words is a sealed state variable. -/
instance : SealedStateVar (Array (UInt64 × UInt64)) := ⟨sealedPairs, rfl⟩

/-- The layout of the sealed nested instance: an array of arrays of machine
words. -/
abbrev sealedNested : Layout := .arr (.arr (.leaf .uint))

/-- An array of arrays of machine words is a sealed state variable: the nested
example, whose write is an update of the inner array. -/
instance : SealedStateVar (Array (Array UInt64)) := ⟨sealedNested, rfl⟩

end SealedStateVar

end Scidonia.FracPerm.StateVar
