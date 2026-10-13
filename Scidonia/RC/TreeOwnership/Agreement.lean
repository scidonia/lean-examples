/-
The library-level results the tree ownership judgement rests on: the per-level
equation of the state replacement, the two effects of that replacement on the
state accessor, the leaf write's frame and snapshot, the concrete pair state those
snapshots are evaluated at, and the conditional take-out transfer of the counted
heap.

**The replacement.** `replaceAt` rebuilds a struct from its updated component and,
at an array, takes the element out of its slot with the layout's default left
behind, replaces the node inside the extracted element, and puts the result back.
`replaceAt_index` writes that array case down as one equation — the take-out, the
recursion on the extracted element, and the put-back — so no level leaves the
placeholder in the array. `replaceAt_subAt` is the replacement's own effect: at an
in-bounds path the accessor at that path reads exactly the state that was
installed, so the replacement writes one node and no other level of the path.
`replaceAt_subAt_of_disjoint` is the frame: an accessor at a path disjoint from the
replaced one — a sibling component, or an element of another index — reads what it
read before, and `replaceAt_nodeVal_of_disjoint` is that same frame at the node
value a read or write rule inspects. The frame is proved by its own induction over
the path rather than as a renaming of the focus equation, because a disjoint
accessor never reaches the level the replacement touched.

**The leaf write.** `read_frame_leaf` and `snapshot_leaf` read the state variable
library's own leaf frame and leaf snapshot at this module's leaf write. The frame
is read at observable leaf paths: the two traversals may share fractional ancestor
nodes, and a borrowed sibling's observable leaf is still unchanged across a
disjoint write, because a write at a leaf path rebuilds exactly the levels on its
own path. The snapshot binds its two reads to their own states — the first to the
state before the write, the second to the state after it — so the value read
before the write is not a second occurrence of the value the write installed.

**The concrete witness.** `snapshot_pair_witness` evaluates one write and its two
reads at one pair state and is decided by the definitions themselves: the left leaf
reads `7` before the write and `9` after it, and the write reports success.

**The take-out transfer.** `takeout_transfer` composes the counted heap's two
whole-heap theorems: a heap counted at the handle list a take-out left and at the
same handles with the account's references after them forces the account to be the
one reference the take-out extracted and forces the account's tags to be injective
on references. The two countings are the caller's counting of one heap at two
handle lists; nothing here reads either of them off a fractional account, and
nothing here reads them off an evaluation.
-/
import Scidonia.RC.TreeOwnership.Judgement
import Scidonia.RC.Transfer

namespace Scidonia.RC

namespace TreeOwnership

open Scidonia.FracPerm.StateVar.Layout5
open Scidonia.FracPerm.StateVar.Footprint (Ref)
open Scidonia.FracPerm.StateVar.RCHeap (CHeap Counted)

/-! ## The replacement's levels -/

/-- The replacement's array case, level by level: at an in-bounds index the
element is taken out of its slot with the layout's default left behind, the
replacement runs on the extracted element, and the result is put back at that
slot. The array is the one it was with that slot set to the replaced node, and no
default survives the level. -/
theorem replaceAt_index {a : Layout} (i : Nat) (q : Path a) (y : State (At q))
    (s : Array (State a)) (h : i < s.size) :
    replaceAt (.arr a) (.index i q) y s = s.set i (replaceAt a q y s[i]) h := by
  show (if h' : i < s.size then
      (s.swapAt i (stateDefault a) h').2.set! i
        (replaceAt a q y (s.swapAt i (stateDefault a) h').1) else s) =
    s.set i (replaceAt a q y s[i]) h
  rw [dite_eq_left h, Array.swapAt_def]
  dsimp only
  rw [Array.set!_eq_setIfInBounds]
  apply Array.ext_getElem?
  intro j
  by_cases hji : i = j
  · subst hji
    simp only [Array.getElem?_setIfInBounds_self_of_lt (xs := s.set i (stateDefault a) h)
      (by simpa using h), Array.getElem?_set_self h]
  · simp only [Array.getElem?_setIfInBounds_ne hji, Array.getElem?_set_ne h hji]

/-- The replacement lands its focus at the path it addressed: at an in-bounds path
the state's own accessor reads back exactly the state that was installed, so the
replacement writes one node and leaves no other level of the path changed. -/
theorem replaceAt_subAt {d : Layout} (p : Path d) (y : State (At p)) (s : State d) :
    InBounds p s → subAt p (replaceAt d p y s) = y := by
  induction p with
  | here =>
      intro _
      rfl
  | left r ih =>
      intro hb
      obtain ⟨u, v⟩ := s
      exact ih y u hb
  | right r ih =>
      intro hb
      obtain ⟨u, v⟩ := s
      exact ih y v hb
  | index i r ih =>
      intro hb
      obtain ⟨e, he, hbq⟩ := hb
      obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp he
      rw [replaceAt_index i r y s hlt, hget, subAt_index,
        Array.getElem?_set_self hlt]
      exact ih y e hbq

/-- The replacement's frame: a read at a path disjoint from the replaced one — a
sibling component, or an element of another index — reads what it read before the
replacement. Disjointness is non-overlap of the whole paths, so the two accesses
share no level the replacement rebuilt. -/
theorem replaceAt_subAt_of_disjoint {d : Layout} (p q : Path d) (y : State (At p))
    (s : State d) : Disjoint p q → InBounds p s → subAt q (replaceAt d p y s) = subAt q s := by
  induction p with
  | here =>
      intro hd _
      exact absurd hd (not_disjoint_here_left q)
  | left r ih =>
      intro hd hb
      obtain ⟨u, v⟩ := s
      cases q with
      | here => exact absurd hd (not_disjoint_here_right (Path.left r))
      | left q' => exact ih q' y u (disjoint_left_iff.mp hd) hb
      | right q' => rfl
  | right r ih =>
      intro hd hb
      obtain ⟨u, v⟩ := s
      cases q with
      | here => exact absurd hd (not_disjoint_here_right (Path.right r))
      | left q' => rfl
      | right q' => exact ih q' y v (disjoint_right_iff.mp hd) hb
  | index i r ih =>
      intro hd hb
      obtain ⟨e, he, hbq⟩ := hb
      obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp he
      cases q with
      | here => exact absurd hd (not_disjoint_here_right (Path.index i r))
      | index j q' =>
          by_cases hij : i = j
          · subst hij
            simp only [replaceAt_index i r y s hlt, hget, subAt_index,
              Array.getElem?_set_self hlt, he]
            exact ih q' y e ((disjoint_index_iff i).mp hd) hbq
          · simp only [replaceAt_index i r y s hlt, subAt_index,
              Array.getElem?_set_ne hlt hij]

/-- The frame at the node value a read or a write inspects: the replacement at a
path leaves the node value at every disjoint path as it was, because the node value
at a path is the quotation of the state that path's own accessor reads. -/
theorem replaceAt_nodeVal_of_disjoint {d : Layout} (p q : Path d) (y : State (At p))
    (s : State d) (hd : Disjoint p q) (hb : InBounds p s) :
    nodeVal q (replaceAt d p y s) = nodeVal q s :=
  congrArg (cellVal (At q)) (replaceAt_subAt_of_disjoint p q y s hd hb)

/-! ## The leaf write's frame and snapshot -/

/-- The leaf write's frame, read at observable leaf paths: a write at one leaf path
leaves what a read at a disjoint leaf path returns unchanged. The two traversals
may share fractional ancestor nodes — `Disjoint` forbids only that either path
continues the other — and the borrowed sibling's observable leaf is unchanged
because the write rebuilds exactly the levels on its own path and no others. -/
theorem read_frame_leaf {d : Layout} (p q : ObsPath d) (s s' : State d) (new : ObsEl p.obs)
    (hd : Disjoint p.path q.path) (hw : setLeaf p new s = (s', true)) :
    read? q s' = read? q s :=
  read_frame p q s s' new hd hw

/-- The read-write-read snapshot at one leaf path: the value read before the write
is the value the first read returned, at the state before the write, and the read
after the write returns the write's own operand, at the state the write left. The
two reads are bound to their own states — the first to the state before the write,
the second to the state after it — so the old value is not a second occurrence of
the new one. -/
theorem snapshot_leaf {d : Layout} (p : ObsPath d) (s s' : State d)
    (old : Scidonia.FracPerm.StateVar.Value) (new : ObsEl p.obs)
    (hr : read? p s = some old) (hw : setLeaf p new s = (s', true)) :
    read? p s = some old ∧ read? p s' = some (encodeObs p.obs new) :=
  snapshot_after_setLeaf p s s' old new hr hw

/-! ## The concrete witness -/

/-- A layout of two natural leaves: a pair whose two components are both read
leaves, so a write at one of them is a write at a leaf path of a state with no
array in it. -/
abbrev pairLayout : Layout := .struct (.leaf .nat) (.leaf .nat)

/-- The state at `pairLayout`: the left leaf holds `7` and the right leaf holds
`9`, so a write at the left leaf changes the first component and leaves the second
one alone. -/
abbrev pairState : State pairLayout := (7, 9)

/-- The path to `pairLayout`'s left component. -/
abbrev pairLeftPath : Path pairLayout := .left (.here : Path (.leaf .nat))

/-- The left component of `pairLayout` as a read path: its end is the natural leaf
that the path's own layout index gives it. -/
abbrev pairLeftObsPath : ObsPath pairLayout := ⟨pairLeftPath, .nat, rfl⟩

/-- The two reads of `pairLeftObsPath` at their own states, evaluated: reading the
left leaf before the write returns `7`, the write reports success, and reading the
left leaf in the state the write left returns `9`. The first read is read at
`pairState` and the second at the state the write produced, which is why the `7`
and the `9` are two different states' values and not two occurrences of one. -/
theorem snapshot_pair_witness :
    read? pairLeftObsPath pairState = some (Scidonia.FracPerm.StateVar.Value.nat 7) ∧
      (setLeaf pairLeftObsPath 9 pairState).2 = true ∧
      read? pairLeftObsPath (setLeaf pairLeftObsPath 9 pairState).1 =
        some (Scidonia.FracPerm.StateVar.Value.nat 9) := by
  decide

/-! ## The conditional take-out transfer -/

/-- The take-out's transfer, composed from the counted heap's two whole-heap
theorems: if the heap counted at `e :: hs` — the handle list a take-out left, with
the extracted occurrence at its head — is counted again at `hs ++ expand m`, the
run's handles followed by the account's references, then the account is that one
extracted occurrence and its tags are injective on references. The two countings
are the caller's counting of the same heap at two handle lists: neither is derived
here from a fractional account, and neither is derived here from an evaluation. -/
theorem takeout_transfer {c : CHeap} {hs : List Ref} {m : Multi} {e : Ref}
    (hrun : Counted c (e :: hs)) (hcouple : Counted c (hs ++ expand m)) :
    expand m = [e] ∧ RefInj m :=
  ⟨expand_eq_singleton_of_counted hrun hcouple, refInj_of_counted hrun hcouple⟩

end TreeOwnership

end Scidonia.RC
