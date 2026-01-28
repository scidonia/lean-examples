import Scidonia.Cyclic.Syntax.Term

namespace Scidonia
namespace Cyclic
namespace Transform

open Scidonia.Cyclic.Syntax

namespace ReadOff

/-- Fix-free node labels for the cyclic term graph. -/
inductive Node : Type
  | nVar (x : Nat)
  | nSort (i : Nat)
  | nPi
  | nLam
  | nApp
  | nInd (ind : Nat)
  | nRoll (ind ctor nparams nrecs : Nat)
  | nCase (ind nbrs : Nat)
  | nSubstNil (k : Nat)
  | nSubstCons (k : Nat)
  | nBack
  deriving Repr

/-- For each de Bruijn index, either it is not recursive (`none`)
    or it points to a cycle-target vertex (`some v`). -/
abbrev BackEnv : Type := List (Option Nat)

/- A lightweight finite map as an association list with shadowing inserts. -/
namespace Assoc

def lookup {α : Type} (xs : List (Nat × α)) (k : Nat) : Option α :=
  match xs.find? (fun kv => kv.1 == k) with
  | none => none
  | some kv => some kv.2

/-- Shadowing insert. -/
def insert {α : Type} (k : Nat) (v : α) (xs : List (Nat × α)) : List (Nat × α) :=
  (k, v) :: xs

end Assoc

/-- Builder state for constructing a cyclic term graph. -/
structure Builder where
  next : Nat
  label : List (Nat × Node)
  succ : List (Nat × List Nat)
  fixTy : List (Nat × Nat)
  fixBody : List (Nat × Nat)
  deriving Repr

/-- Empty builder. -/
def emptyBuilder : Builder :=
  { next := 0, label := [], succ := [], fixTy := [], fixBody := [] }

/-- Allocate a fresh vertex id. -/
def fresh (b : Builder) : Nat × Builder :=
  let v := b.next
  (v, { b with next := v + 1 })

/-- Fill a vertex with a label and successor list. -/
def put (v : Nat) (lbl : Node) (succs : List Nat) (b : Builder) : Builder :=
  { b with
    label := Assoc.insert v lbl b.label
    succ := Assoc.insert v succs b.succ }

/-- Record the type vertex for a cycle target. -/
def putFixTy (v vA : Nat) (b : Builder) : Builder :=
  { b with fixTy := Assoc.insert v vA b.fixTy }

/-- Record the body root vertex for a cycle target. -/
def putFixBody (v vBody : Nat) (b : Builder) : Builder :=
  { b with fixBody := Assoc.insert v vBody b.fixBody }

/-- Decompose an application spine into head and arguments (left-associated). -/
def appView : Tm → Tm × List Tm
  | Tm.app t u =>
      let (h, args) := appView t
      (h, args ++ [u])
  | t => (t, [])

/-- Compilation fuel for terms.

We use a simple size-based upper bound. This intentionally over-approximates the
fuel needed by `compileTm`/`compileList`, but keeps this pass purely
computational without additional termination proofs.
 -/
def fuelTm (t : Tm) : Nat :=
  2 * Nat.succ (Tm.size t)

/-- Build a substitution evidence chain from a list of argument vertices.

`sv_tail` should be the `nSubstNil` vertex. -/
def buildSubstChain : List Nat → Nat → Builder → Nat × Builder
  | [], svTail, b => (svTail, b)
  | u :: us, svTail, b =>
      let (svTail', b1) := buildSubstChain us svTail b
      let (svHead, b2) := fresh b1
      (svHead, put svHead (Node.nSubstCons 0) [u, svTail'] b2)

mutual

  /-- Compile a term into the fix-free cyclic graph representation. -/
  def compileTm : Nat → BackEnv → Tm → Builder → Nat × Builder
    | 0, _, _, b =>
        let (v, b1) := fresh b
        (v, put v (Node.nVar 0) [] b1)
    | Nat.succ fuel, ρ, t, b =>
        match t with
        | Tm.var x =>
            let (v, b1) := fresh b
            (v, put v (Node.nVar x) [] b1)
        | Tm.sort i =>
            let (v, b1) := fresh b
            (v, put v (Node.nSort i) [] b1)
        | Tm.pi A B =>
            let (vA, b1) := compileTm fuel ρ A b
            let (vB, b2) := compileTm fuel (none :: ρ) B b1
            let (v, b3) := fresh b2
            (v, put v Node.nPi [vA, vB] b3)
        | Tm.lam A t =>
            let (vA, b1) := compileTm fuel ρ A b
            let (vt, b2) := compileTm fuel (none :: ρ) t b1
            let (v, b3) := fresh b2
            (v, put v Node.nLam [vA, vt] b3)
        | Tm.app t1 u1 =>
            let (h, args) := appView t
            match h with
            | Tm.var x =>
                match ρ[x]? with
                | some (some target) =>
                    let (vArgs, b1) := compileList fuel ρ args b
                    let (svNil, b2) := fresh b1
                    let b3 := put svNil (Node.nSubstNil 0) [] b2
                    let (sv, b4) := buildSubstChain vArgs svNil b3
                    let (v, b5) := fresh b4
                    (v, put v Node.nBack [target, sv] b5)
                | _ =>
                    let (v1, b1) := compileTm fuel ρ t1 b
                    let (v2, b2) := compileTm fuel ρ u1 b1
                    let (v, b3) := fresh b2
                    (v, put v Node.nApp [v1, v2] b3)
            | _ =>
                let (v1, b1) := compileTm fuel ρ t1 b
                let (v2, b2) := compileTm fuel ρ u1 b1
                let (v, b3) := fresh b2
                (v, put v Node.nApp [v1, v2] b3)
        | Tm.fix A body =>
            let (v, b0) := fresh b
            let (vA, b1) := compileTm fuel ρ A b0
            let b1' := putFixTy v vA b1
            let (vBody, b2) := compileTm fuel (some v :: ρ) body b1'
            let b2' := putFixBody v vBody b2
            (v, b2')
        | Tm.ind ind =>
            let (v, b1) := fresh b
            (v, put v (Node.nInd ind) [] b1)
        | Tm.roll ind ctor params recs =>
            let (vps, b1) := compileList fuel ρ params b
            let (vrs, b2) := compileList fuel ρ recs b1
            let (v, b3) := fresh b2
            (v, put v (Node.nRoll ind ctor vps.length vrs.length) (vps ++ vrs) b3)
        | Tm.case ind scrut C brs =>
            let (vScrut, b1) := compileTm fuel ρ scrut b
            let (vC, b2) := compileTm fuel ρ C b1
            let (vBrs, b3) := compileList fuel ρ brs b2
            let (v, b4) := fresh b3
            (v, put v (Node.nCase ind vBrs.length) ([vScrut, vC] ++ vBrs) b4)

  /-- Compile a list of terms, consuming one fuel step per list cell. -/
  def compileList : Nat → BackEnv → List Tm → Builder → List Nat × Builder
    | 0, _, _, b => ([], b)
    | Nat.succ fuel, ρ, ts, b =>
        match ts with
        | [] => ([], b)
        | t :: ts =>
            let (v, b1) := compileTm fuel ρ t b
            let (vs, b2) := compileList fuel ρ ts b1
            (v :: vs, b2)

end

/-- Compile a term to a raw cyclic graph. -/
def readOffRaw (t : Tm) : Nat × Builder :=
  compileTm (fuelTm t) [] t emptyBuilder

end ReadOff

end Transform
end Cyclic
end Scidonia
