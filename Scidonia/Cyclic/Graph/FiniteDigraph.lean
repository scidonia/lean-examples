namespace Scidonia
namespace Cyclic
namespace Graph

/-- A finite directed graph where `succ` is a total function, but only constrained
on the declared vertex set `verts` via `succ_closed`. -/
structure FinDigraph (V : Type u) [DecidableEq V] where
  verts : List V
  succ : V → List V
  succ_closed : ∀ v, v ∈ verts → (succ v).all (fun w => w ∈ verts)

namespace FinDigraph

variable {V : Type u} [DecidableEq V]

def edge (G : FinDigraph V) (v w : V) : Prop :=
  v ∈ G.verts ∧ w ∈ G.succ v

def outNeighbours (G : FinDigraph V) (v : V) : List V :=
  G.succ v

def last? : List V → Option V
  | [] => none
  | [x] => some x
  | _ :: xs' => last? xs'

def edgesFrom (G : FinDigraph V) (v : V) : List V → Prop
  | [] => True
  | w :: xs => w ∈ G.succ v ∧ edgesFrom G w xs

def edgesAlong (G : FinDigraph V) : List V → Prop
  | [] => True
  | v :: xs => edgesFrom G v xs

def isPath (G : FinDigraph V) (xs : List V) : Prop :=
  xs.all (fun v => v ∈ G.verts) ∧ edgesAlong G xs

def isPathFrom (G : FinDigraph V) (v : V) (xs : List V) : Prop :=
  xs.head? = some v ∧ isPath G xs

def isPathTo (G : FinDigraph V) (v : V) (xs : List V) : Prop :=
  last? xs = some v ∧ isPath G xs

def isCycle (G : FinDigraph V) (xs : List V) : Prop :=
  ∃ v ys, xs = v :: ys ++ [v] ∧ ys ≠ [] ∧ isPath G xs

def reachableByPath (G : FinDigraph V) (v w : V) : Prop :=
  ∃ xs, isPathFrom G v xs ∧ isPathTo G w xs

theorem succ_mem_verts (G : FinDigraph V) (v w : V) :
    v ∈ G.verts → w ∈ G.succ v → w ∈ G.verts := by
  intro hv hw
  have hclosed := G.succ_closed v hv
  simp [List.all_eq_true] at hclosed
  exact hclosed w hw

inductive Reachable (G : FinDigraph V) : V → V → Prop
  | refl (v : V) : v ∈ G.verts → Reachable G v v
  | step (v w u : V) :
      v ∈ G.verts →
      w ∈ G.succ v →
      Reachable G w u →
      Reachable G v u

namespace Reachable

theorem edge (G : FinDigraph V) (v w : V) :
    FinDigraph.edge G v w → Reachable G v w := by
  intro h
  rcases h with ⟨hv, hw⟩
  apply Reachable.step v w w hv hw
  apply Reachable.refl
  exact succ_mem_verts (G := G) (v := v) (w := w) hv hw

theorem trans (G : FinDigraph V) (v w u : V) :
    Reachable G v w → Reachable G w u → Reachable G v u := by
  intro hvw hwu
  induction hvw with
  | refl v hv =>
      simpa using hwu
  | step v x w hv hvx hxw ih =>
      exact Reachable.step v x u hv hvx (ih hwu)

end Reachable

def mutReachable (G : FinDigraph V) (v w : V) : Prop :=
  Reachable G v w ∧ Reachable G w v

theorem mutReachable_refl (G : FinDigraph V) (v : V) :
    v ∈ G.verts → mutReachable G v v := by
  intro hv
  constructor
  · exact Reachable.refl v hv
  · exact Reachable.refl v hv

theorem mutReachable_symm (G : FinDigraph V) (v w : V) :
    mutReachable G v w → mutReachable G w v := by
  intro h
  exact ⟨h.2, h.1⟩

theorem mutReachable_trans (G : FinDigraph V) (u v w : V) :
    mutReachable G u v → mutReachable G v w → mutReachable G u w := by
  intro huv hvw
  refine ⟨?_, ?_⟩
  · exact Reachable.trans (G := G) u v w huv.1 hvw.1
  · exact Reachable.trans (G := G) w v u hvw.2 huv.2

def stronglyConnected (G : FinDigraph V) (S : List V) : Prop :=
  (∀ v, v ∈ S → v ∈ G.verts) ∧ (∀ u v, u ∈ S → v ∈ S → mutReachable G u v)

def isScc (G : FinDigraph V) (S : List V) : Prop :=
  S ≠ [] ∧ stronglyConnected G S ∧
  (∀ T, stronglyConnected G T → (∀ v, v ∈ S → v ∈ T) → (∀ v, v ∈ T → v ∈ S))

theorem isScc_stronglyConnected (G : FinDigraph V) (S : List V) :
    isScc G S → stronglyConnected G S := by
  intro h
  exact h.2.1

end FinDigraph

end Graph
end Cyclic
end Scidonia
