import Scidonia.Cyclic.Graph.FiniteDigraph
import Scidonia.Cyclic.Preproof.Preproof
import Scidonia.Cyclic.Transform.ReadOff

namespace Scidonia
namespace Cyclic
namespace Transform

open Scidonia.Cyclic.Graph
open Scidonia.Cyclic.Preproof

namespace ReadOffPreproof

abbrev V : Type := Nat

/-- Vertex-based judgements used to label a read-off graph.

This is a *lightweight* packaging step: it gives us a `RootedPreproof` object
that can later be strengthened into real typing/equality goals.
-/
inductive Judgement : Type
  | jSub (sv : V)
  | jTy (v : V)
  deriving Repr

/-- Vertex bound used for packaging.

We include all vertices `0 .. b.next-1` and also force inclusion of the chosen
root.
-/
def bound (root : V) (b : ReadOff.Builder) : Nat :=
  Nat.succ (Nat.max root b.next)

/-- All vertices below `bound root b` are considered present. -/
def vertsOf (root : V) (b : ReadOff.Builder) : List V :=
  List.range (bound root b)

/-- Successors of a vertex, filtered to the vertex set. -/
def succOf (root : V) (b : ReadOff.Builder) (v : V) : List V :=
  let xs :=
    match ReadOff.Assoc.lookup b.succ v with
    | some ys => ys
    | none => []
  xs.filter (fun w => w < bound root b)

/-- Lookup node label with a default. -/
def labelOf (b : ReadOff.Builder) (v : V) : ReadOff.Node :=
  match ReadOff.Assoc.lookup b.label v with
  | some n => n
  | none => ReadOff.Node.nVar 0

def ppLabel (b : ReadOff.Builder) (v : V) : Judgement :=
  match labelOf b v with
  | ReadOff.Node.nSubstNil _ => Judgement.jSub v
  | ReadOff.Node.nSubstCons _ => Judgement.jSub v
  | _ => Judgement.jTy v

/-- A permissive rule relation for packaging.

For now we only insist that substitution evidence nodes are labelled `jSub`;
all other nodes are accepted.
-/
def Rule (b : ReadOff.Builder) (j : Judgement) (_premises : List Judgement) : Prop :=
  match j with
  | Judgement.jSub sv =>
      match labelOf b sv with
      | ReadOff.Node.nSubstNil _ => True
      | ReadOff.Node.nSubstCons _ => True
      | _ => False
  | Judgement.jTy _ => True

theorem succOf_closed (root : V) (b : ReadOff.Builder) (v : V) :
    v ∈ vertsOf root b → (succOf root b v).all (fun w => w ∈ vertsOf root b) := by
  intro _
  unfold succOf vertsOf bound
  simp

/-- Graph view of a builder, for preproof packaging. -/
def graphOf (root : V) (b : ReadOff.Builder) : FinDigraph V :=
  { verts := vertsOf root b
    succ := succOf root b
    succ_closed := succOf_closed root b }

theorem ppRuleOk (root : V) (b : ReadOff.Builder) (v : V) :
    v ∈ (graphOf root b).verts →
    Rule b (ppLabel b v) (((graphOf root b).succ v).map (ppLabel b)) := by
  intro _
  cases hnode : labelOf b v <;> simp [Rule, ppLabel, hnode]

/-- Package a builder as a preproof. -/
def preproofOf (root : V) (b : ReadOff.Builder) : Preproof Judgement (Rule b) V :=
  { graph := graphOf root b
    label := ppLabel b
    rule_ok := fun v hv => ppRuleOk root b v hv }

/-- Rooted preproof produced by read-off. -/
def rootedPreproofOf (t : Syntax.Tm) :
    RootedPreproof Judgement (Rule (ReadOff.readOffRaw t).2) V := by
  classical
  refine (match ReadOff.readOffRaw t with
    | (root, b) => ?_)
  refine { proof := preproofOf root b, root := root, root_in := ?_ }
  unfold preproofOf graphOf vertsOf bound
  simpa [List.mem_range] using (Nat.lt_succ_of_le (Nat.le_max_left root b.next))

end ReadOffPreproof

end Transform
end Cyclic
end Scidonia
