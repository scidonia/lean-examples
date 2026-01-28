import Scidonia.Cyclic.Graph.FiniteDigraph

namespace Scidonia
namespace Cyclic
namespace Progress

open Scidonia.Cyclic.Graph

namespace Ranking

universe u v

variable {V : Type u} [DecidableEq V]
variable (G : FinDigraph V)
variable (progressEdge : V → V → Prop)
variable {M : Type v}
variable (ltM : M → M → Prop)
variable (rank : V → M)

/-- Reflexive closure of a strict order. (Coq's `clos_refl`.) -/
def leM (a b : M) : Prop := a = b ∨ ltM a b

def rankMonotone : Prop :=
  ∀ v w, FinDigraph.edge G v w → leM ltM (rank w) (rank v)

def rankStrictOnProgress : Prop :=
  ∀ v w, FinDigraph.edge G v w → progressEdge v w → ltM (rank w) (rank v)

def hasProgressEdgeFrom (v : V) : List V → Prop
  | [] => False
  | w :: xs => progressEdge v w ∨ hasProgressEdgeFrom w xs

def hasProgressEdge : List V → Prop
  | [] => False
  | v :: xs => hasProgressEdgeFrom (progressEdge := progressEdge) v xs

theorem hasProgressEdgeFrom_cons (v w : V) (xs : List V) :
    hasProgressEdgeFrom (progressEdge := progressEdge) v (w :: xs) ↔
      progressEdge v w ∨ hasProgressEdgeFrom (progressEdge := progressEdge) w xs := by
  simp [hasProgressEdgeFrom]

theorem hasProgressEdge_cons (v : V) (xs : List V) :
    hasProgressEdge (progressEdge := progressEdge) (v :: xs) ↔
      hasProgressEdgeFrom (progressEdge := progressEdge) v xs := by
  simp [hasProgressEdge]

/-- Ranking-based global soundness condition.

Intuition:
- along every edge rank does not increase (`rankMonotone`)
- along progress edges it strictly decreases (`rankStrictOnProgress`)
- every directed cycle contains at least one progress edge. -/
structure Condition : Prop where
  wf : WellFounded ltM
  monotone : rankMonotone (G := G) (ltM := ltM) (rank := rank)
  strict : rankStrictOnProgress (G := G) (progressEdge := progressEdge) (ltM := ltM) (rank := rank)
  cycle_progress : ∀ xs, FinDigraph.isCycle G xs → hasProgressEdge (progressEdge := progressEdge) xs

end Ranking

end Progress
end Cyclic
end Scidonia
