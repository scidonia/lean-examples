import Scidonia.Cyclic.Syntax.Term
import Scidonia.Cyclic.Transform.ReadOff

namespace Scidonia
namespace Cyclic
namespace Transform

open Scidonia.Cyclic.Syntax

namespace Extract

namespace RO := ReadOff

/-- A fixpoint environment mapping cycle-target vertices to de Bruijn indices. -/
abbrev FixEnv : Type := List (Nat × Nat)

namespace Assoc

def lookup (xs : List (Nat × Nat)) (k : Nat) : Option Nat :=
  match xs.find? (fun kv => kv.1 == k) with
  | none => none
  | some kv => some kv.2

def insert (k v : Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  (k, v) :: xs

end Assoc

def envShift (ρ : FixEnv) : FixEnv :=
  ρ.map (fun kv => (kv.1, kv.2 + 1))

def apps (t : Tm) (us : List Tm) : Tm :=
  us.foldl (fun acc u => Tm.app acc u) t

def lookupNode (b : RO.Builder) (v : Nat) : RO.Node :=
  match RO.Assoc.lookup b.label v with
  | some n => n
  | none => RO.Node.nVar 0

def lookupSucc (b : RO.Builder) (v : Nat) : List Nat :=
  match RO.Assoc.lookup b.succ v with
  | some xs => xs
  | none => []

def lookupFixTy (b : RO.Builder) (v : Nat) : Option Nat :=
  RO.Assoc.lookup b.fixTy v

def lookupFixBody (b : RO.Builder) (v : Nat) : Option Nat :=
  RO.Assoc.lookup b.fixBody v

/-- Extract a list of vertices, consuming fuel across the list. -/
def extractList
    (ev : Nat → RO.Builder → FixEnv → Nat → Tm)
    : Nat → RO.Builder → FixEnv → List Nat → List Tm
  | 0, _, _, _ => []
  | Nat.succ fuel, b, ρ, vs =>
      match vs with
      | [] => []
      | v :: vs => ev fuel b ρ v :: extractList ev fuel b ρ vs

mutual

  /-- Extract a term from a vertex, synthesizing `Tm.fix` at cycle targets. -/
  def extractV : Nat → RO.Builder → FixEnv → Nat → Tm
    | 0, _, _, _ => Tm.var 0
    | Nat.succ fuel, b, ρ, v =>
        match Assoc.lookup ρ v with
        | some k => Tm.var k
        | none =>
            match lookupFixTy b v with
            | some vA =>
                let A := extractV fuel b ρ vA
                let ρ' := Assoc.insert v 0 (envShift ρ)
                let body :=
                  match lookupFixBody b v with
                  | some vBody => extractV fuel b ρ' vBody
                  | none => extractNode fuel b ρ' v
                Tm.fix A body
            | none =>
                extractNode fuel b ρ v

  /-- Extract a term from the node label at a vertex. -/
  def extractNode : Nat → RO.Builder → FixEnv → Nat → Tm
    | 0, _, _, _ => Tm.var 0
    | Nat.succ fuel, b, ρ, v =>
        match lookupNode b v with
        | RO.Node.nVar x => Tm.var x
        | RO.Node.nSort i => Tm.sort i
        | RO.Node.nPi =>
            match lookupSucc b v with
            | [vA, vB] =>
                let A := extractV fuel b ρ vA
                let B := extractV fuel b (envShift ρ) vB
                Tm.pi A B
            | _ => Tm.var 0
        | RO.Node.nLam =>
            match lookupSucc b v with
            | [vA, vt] =>
                let A := extractV fuel b ρ vA
                let t := extractV fuel b (envShift ρ) vt
                Tm.lam A t
            | _ => Tm.var 0
        | RO.Node.nApp =>
            match lookupSucc b v with
            | [vf, va] => Tm.app (extractV fuel b ρ vf) (extractV fuel b ρ va)
            | _ => Tm.var 0
        | RO.Node.nInd ind => Tm.ind ind
        | RO.Node.nRoll ind ctor nparams nrecs =>
            let xs := lookupSucc b v
            let ps := xs.take nparams
            let rs := xs.drop nparams
            Tm.roll ind ctor
              (extractList extractV (Nat.succ fuel) b ρ ps)
              (extractList extractV (Nat.succ fuel) b ρ rs)
        | RO.Node.nCase ind nbrs =>
            match lookupSucc b v with
            | vScrut :: vC :: brs =>
                Tm.case ind (extractV fuel b ρ vScrut) (extractV fuel b ρ vC)
                  (extractList extractV (Nat.succ fuel) b ρ (brs.take nbrs))
            | _ => Tm.var 0
        | RO.Node.nSubstNil _ => Tm.var 0
        | RO.Node.nSubstCons _ => Tm.var 0
        | RO.Node.nBack =>
            match lookupSucc b v with
            | [target, sv] =>
                match Assoc.lookup ρ target with
                | some k => apps (Tm.var k) (substArgs fuel b ρ sv)
                | none => Tm.var 0
            | _ => Tm.var 0

  /-- Extract substitution arguments from an explicit substitution chain. -/
  def substArgs : Nat → RO.Builder → FixEnv → Nat → List Tm
    | 0, _, _, _ => []
    | Nat.succ fuel, b, ρ, sv =>
        match lookupNode b sv with
        | RO.Node.nSubstNil _ => []
        | RO.Node.nSubstCons _ =>
            match lookupSucc b sv with
            | [u, svTail] => extractV fuel b ρ u :: substArgs fuel b ρ svTail
            | _ => []
        | _ => []

end

/-- Extract a term from a builder and root vertex.

Fuel is chosen based on builder size. -/
def extract (b : RO.Builder) (root : Nat) : Tm :=
  extractV (2 * (b.next + 1)) b ([] : FixEnv) root

/-- Extract a term from `ReadOff.readOffRaw t` using a size-based fuel. -/
def extractReadOff (t : Tm) : Tm :=
  let (root, b) := RO.readOffRaw t
  extractV (2 * Nat.succ (Tm.size t)) b ([] : FixEnv) root

end Extract

end Transform
end Cyclic
end Scidonia
