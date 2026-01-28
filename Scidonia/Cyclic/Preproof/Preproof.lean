import Scidonia.Cyclic.Graph.FiniteDigraph

namespace Scidonia
namespace Cyclic
namespace Preproof

open Scidonia.Cyclic.Graph

universe u v

/-- A (finite) graph-shaped derivation with locally correct rule instances. -/
structure Preproof (Judgement : Type u)
    (Rule : Judgement → List Judgement → Prop)
    (V : Type v) [DecidableEq V] where
  graph : FinDigraph V
  label : V → Judgement
  rule_ok : ∀ v,
    v ∈ graph.verts →
    Rule (label v) ((graph.succ v).map label)

/-- A preproof equipped with a distinguished root node. -/
structure RootedPreproof (Judgement : Type u)
    (Rule : Judgement → List Judgement → Prop)
    (V : Type v) [DecidableEq V] where
  proof : Preproof Judgement Rule V
  root : V
  root_in : root ∈ proof.graph.verts

end Preproof
end Cyclic
end Scidonia
