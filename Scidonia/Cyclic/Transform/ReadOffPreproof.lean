import Scidonia.Cyclic.Graph.FiniteDigraph
import Scidonia.Cyclic.Preproof.Preproof
import Scidonia.Cyclic.Transform.ReadOff

namespace Scidonia
namespace Cyclic
namespace Transform

open Scidonia.Cyclic.Graph
open Scidonia.Cyclic.Preproof

namespace ReadOffPreproof

namespace RO := ReadOff

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
def bound (root : V) (b : RO.Builder) : Nat :=
  Nat.succ (Nat.max root b.next)

/-- All vertices below `bound root b` are considered present. -/
def vertsOf (root : V) (b : RO.Builder) : List V :=
  List.range (bound root b)

/-- Successors of a vertex, filtered to the vertex set. -/
def succOf (root : V) (b : RO.Builder) (v : V) : List V :=
  let xs :=
    match RO.Assoc.lookup b.succ v with
    | some ys => ys
    | none => []
  xs.filter (fun w => w < bound root b)

/-- Lookup node label with a default. -/
def labelOf (b : RO.Builder) (v : V) : RO.Node :=
  match RO.Assoc.lookup b.label v with
  | some n => n
  | none => RO.Node.nVar 0

def ppLabel (b : RO.Builder) (v : V) : Judgement :=
  match labelOf b v with
  | RO.Node.nSubstNil _ => Judgement.jSub v
  | RO.Node.nSubstCons _ => Judgement.jSub v
  | _ => Judgement.jTy v

/-- A permissive rule relation for packaging.

For now we only insist that substitution evidence nodes are labelled `jSub`;
all other nodes are accepted.
-/
def Rule (b : RO.Builder) (j : Judgement) (_premises : List Judgement) : Prop :=
  match j with
  | Judgement.jSub sv =>
      match labelOf b sv with
      | RO.Node.nSubstNil _ => True
      | RO.Node.nSubstCons _ => True
      | _ => False
  | Judgement.jTy _ => True

theorem succOf_closed (root : V) (b : RO.Builder) (v : V) :
    v ∈ vertsOf root b → (succOf root b v).all (fun w => w ∈ vertsOf root b) := by
  intro _
  unfold succOf vertsOf bound
  simp

/-- Graph view of a builder, for preproof packaging. -/
def graphOf (root : V) (b : RO.Builder) : FinDigraph V :=
  { verts := vertsOf root b
    succ := succOf root b
    succ_closed := succOf_closed root b }

theorem ppRuleOk (root : V) (b : RO.Builder) (v : V) :
    v ∈ (graphOf root b).verts →
    Rule b (ppLabel b v) (((graphOf root b).succ v).map (ppLabel b)) := by
  intro _
  -- rule ignores premises, so it suffices to check the node kind.
  unfold Rule ppLabel
  cases h : labelOf b v <;> simp [labelOf] at h <;> simp [h]

/-- Package a builder as a preproof. -/
def preproofOf (root : V) (b : RO.Builder) : Preproof Judgement (Rule b) V :=
  { graph := graphOf root b
    label := ppLabel b
    rule_ok := fun v hv => ppRuleOk root b v hv }

/-- Rooted preproof produced by read-off. -/
def rootedPreproofOf (t : Syntax.Tm) :
    RootedPreproof Judgement (Rule (snd (RO.readOffRaw t))) V := by
  classical
  refine (match RO.readOffRaw t with
    | (root, b) => ?_)
  refine { proof := preproofOf root b, root := root, root_in := ?_ }
  -- root is in `range (succ (max root b.next))` by construction.
  unfold preproofOf graphOf vertsOf bound
  simpa [List.mem_range] using (Nat.lt_succ_of_le (Nat.le_max_left root b.next))

end ReadOffPreproof

end Transform
end Cyclic
end Scidonia
