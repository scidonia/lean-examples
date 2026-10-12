/-
Compile-time check of the IR the pinned toolchain emits for the library's write
paths.

`IR.findEnvDecl` answers with the post-reference-counting IR of a declaration —
body included — for this library's own declarations, to a module that merely
imports them, so what the check reads is the code the toolchain compiled into the
olean this build imported, and not the source text. It names the declarations it
reads and asserts the *shape* recorded for them: the shape
`FracPerm_Linearity_Proposal.md` §3.6 measures and the module note of
`StateVar/Layout5.lean` describes. An update that takes its element out appears
as `Array.getInternal` beside a placeholder `Array.set`; a bounds walk reads its
element with `Array.getInternalBorrowed`; a rebuild of a whole value tests
`isShared` and writes the cell with `set`; and the structured executor's `set`
case writes with `Array.set!`. Every elaboration of this module prints the survey
and each requirement's outcome, and throws when a requirement does not hold, so
building the check library is the gate.

Three things the check does not say.

* It is not an ownership property and not a reference count. The IR names an
  `isShared` test and a cell `set`, whose own specification in
  `Lean.Compiler.IR.Basic` requires a count of one; whether the count is one
  where the write runs is a run-time fact the IR does not carry.
* It says nothing about whether a compiled write mutates its object. An array
  element write decides that outside the IR: `Array.set`, behind
  `@[extern "lean_array_fset"]`, and `Array.set!`, behind
  `@[extern "lean_array_set"]`, both reach `lean_array_uset`, which calls
  `lean_ensure_exclusive_array` and so `lean_is_exclusive`, in the runtime
  header. No assertion here reaches that; `ScidoniaInPlace` is what observes an
  address, and a copy.
* A body may hold both shapes. `setLeaf`'s rebuild holds the cell `set` and a
  fresh `ctor_0[Prod.mk]` in its two branches, so nothing here asserts the
  absence of an allocation; and a whole declaration is not the code at one site,
  so where a specific case of a `case` is meant, the requirement reads that
  alternative alone.

Two readings keep a requirement from being satisfied by code that never runs
that way. A requirement about what a body *names* reads the body as a whole, with
the alternatives of a `case` side by side; a requirement about an *order* or an
*operand flow* reads one executing path through the alternative it is about and
binds the variables the calls pass on, so a check whose result is discarded, a
write through an unchecked array, or a sequence assembled from two branches that
cannot both run does not satisfy it. The report marks which reading each
requirement used.

The route. `IR.findEnvDecl` returns bodies for this library because these sources
are not `module`-keyword modules: lake marks them `isModule=false`, and their
olean carries the complete entry for each declaration rather than an `extern`
stub. If a source gains `module`, or the IR moves to separate `.ir` parts, the
route needs re-verifying — and the check fails closed, because the declarations
it names would then have no body, which is a failure here rather than a pass.

A declaration's own entry is a stub that calls its arity-reduced `_redArg`
variant, so the check reads that variant; and a `private` declaration is asked
for under the name the compiler mangles it into, built with `mkPrivateNameCore`.
-/
import Lean.Elab.Command
import Lean.Compiler.IR.CompilerM
import Scidonia.FracPerm.StateVar.Layout5
import Scidonia.FracPerm.Structured.Executor

open Lean
open Lean.Elab.Command

namespace ScidoniaTest.IRShape

/-! ## Reading a declaration's IR

Two readings of a body answer two kinds of requirement.

`constructsOf` records every construct the requirements below ask about, in the
order the body holds them and with the alternatives of a `case` one after the
other: the calls a body makes with the operands they are applied to and the
variable each is bound to, the projections it takes, the `isShared` tests it
makes, the reference-count steps it takes and the cells it writes with `set`. A
requirement about what a body *names* anywhere reads that.

`pathsOf` records the same constructs one executing path at a time: it follows a
single alternative at every nested `case` and continues into a join point where
the path jumps to one, so the calls a path holds are calls that can occur
together. A requirement about an *order* or a *flow* reads that, so a sequence
assembled from two alternatives of one `case` does not satisfy it.

`altBody?` reaches one alternative of a `case` — the array step of a path
recursion, or the `set` case of the executor — by the constructor name it
matches. -/

/-- One construct of a body's IR. -/
inductive Construct where
  /-- A full or partial application of a function, applied to `args` and, when
  the body binds the application with `let`, bound to the variable in `bound?`. -/
  | call (f : IR.FunId) (args : Array IR.Arg) (bound? : Option IR.VarId)
  /-- A projection of field `field` of a constructor object into a variable. -/
  | proj (field : Nat) (x : IR.VarId) (bound : IR.VarId)
  /-- A test of whether an object is shared. -/
  | testShared (x : IR.VarId)
  /-- A reference-count increment. -/
  | incRef (x : IR.VarId)
  /-- A reference-count decrement. -/
  | decRef (x : IR.VarId)
  /-- A write of a constructor object's cell. -/
  | cellSet (x : IR.VarId) (i : Nat)

/-- The construct an expression is, when it is one of the constructs above.
`bound?` is the variable a `let` in the holding body binds the expression to; a
projection is only a construct where one does. -/
def constructOfExpr (e : IR.Expr) (bound? : Option IR.VarId) : Option Construct :=
  match e with
  | .fap f args => some (.call f args bound?)
  | .pap f args => some (.call f args bound?)
  | .isShared x => some (.testShared x)
  | .proj field x => bound?.map fun bound => .proj field x bound
  | _ => none

/-- The constructs a body holds, in the order the body holds them: a join point's
own body first, then the body into which it was declared, and the alternatives of
a `case` one after the other. -/
partial def constructsOf (b : IR.FnBody) : Array Construct :=
  match b with
  | .vdecl x _ e rest => (constructOfExpr e (some x)).toArray ++ constructsOf rest
  | .jdecl _ _ value rest => constructsOf value ++ constructsOf rest
  | .set x i _ rest => #[.cellSet x i] ++ constructsOf rest
  | .setTag _ _ rest => constructsOf rest
  | .uset _ _ _ rest => constructsOf rest
  | .sset _ _ _ _ _ rest => constructsOf rest
  | .inc x _ _ _ rest => #[.incRef x] ++ constructsOf rest
  | .dec x _ _ _ rest => #[.decRef x] ++ constructsOf rest
  | .del _ rest => constructsOf rest
  | .case _ _ _ alts => alts.foldl (fun acc a => acc ++ constructsOf a.body) #[]
  | .ret _ => #[]
  | .jmp _ _ => #[]
  | .unreachable => #[]

/-- The constructs of each executing path through a body, in execution order: one
entry per combination of the alternatives its nested `case`s can take. A jump
into a join point declared around the body continues along that join point's own
paths; a jump back into a join point the path already entered ends the path
there, since that join point's constructs are on the path already. -/
partial def pathsFrom (joins : Array (IR.JoinPointId × IR.FnBody)) (b : IR.FnBody) :
    Array (Array Construct) :=
  match b with
  | .vdecl x _ e rest =>
    match constructOfExpr e (some x) with
    | some c => (pathsFrom joins rest).map fun tail => #[c] ++ tail
    | none => pathsFrom joins rest
  | .jdecl j _ value rest => pathsFrom (joins.push (j, value)) rest
  | .set x i _ rest => (pathsFrom joins rest).map fun tail => #[.cellSet x i] ++ tail
  | .setTag _ _ rest => pathsFrom joins rest
  | .uset _ _ _ rest => pathsFrom joins rest
  | .sset _ _ _ _ _ rest => pathsFrom joins rest
  | .inc x _ _ _ rest => (pathsFrom joins rest).map fun tail => #[.incRef x] ++ tail
  | .dec x _ _ _ rest => (pathsFrom joins rest).map fun tail => #[.decRef x] ++ tail
  | .del _ rest => pathsFrom joins rest
  | .case _ _ _ alts => alts.foldl (fun acc a => acc ++ pathsFrom joins a.body) #[]
  | .jmp j _ =>
    match joins.findSome? (fun p => if p.1 == j then some p.2 else none) with
    | some value => pathsFrom (joins.filter (fun p => p.1 != j)) value
    | none => #[#[]]
  | .ret _ => #[#[]]
  | .unreachable => #[#[]]

/-- The executing paths through a body, with no join point in scope. -/
partial def pathsOf (b : IR.FnBody) : Array (Array Construct) := pathsFrom #[] b

/-- The calls a body's constructs hold, in order, repeats included. -/
def callsOf (cs : Array Construct) : Array IR.FunId :=
  cs.filterMap fun c => match c with | .call f _ _ => some f | _ => none

/-- Whether a body names `f`. -/
def namesCall (cs : Array Construct) (f : IR.FunId) : Bool :=
  cs.any fun c => match c with | .call g _ _ => g == f | _ => false

/-- Whether a body tests any object for sharing. -/
def namesShared (cs : Array Construct) : Bool :=
  cs.any fun c => match c with | .testShared _ => true | _ => false

/-- Whether a body writes a constructor object's cell. -/
def writesCell (cs : Array Construct) : Bool :=
  cs.any fun c => match c with | .cellSet _ _ => true | _ => false

/-- True when `fs` occur among the body's calls in this order; other calls may
stand between them. -/
def callsInOrder (cs : Array Construct) (fs : List IR.FunId) : Bool :=
  (callsOf cs).foldl (init := fs) (fun remaining f =>
    match remaining with
    | expected :: rest => if expected == f then rest else remaining
    | [] => []) == []

/-- The variables an application is applied to, in order, with erased arguments
left out, so that an operand position counts the same way whatever the callee
erases. -/
def varArgs (args : Array IR.Arg) : Array IR.VarId :=
  args.filterMap fun a => match a with | .var x => some x | .erased => none

/-- The variable an application takes at variable-argument position `n`. -/
def argAt (args : Array IR.Arg) (n : Nat) : Option IR.VarId := (varArgs args)[n]?

/-- The positions of a path from `start` on, which the flow checks walk. -/
def positionsFrom (cs : Array Construct) (start : Nat) : List Nat :=
  (List.range cs.size).filter fun i => decide (start ≤ i)

/-- Whether a path holds a call to `f` bound to a variable and, later on the same
path, a call to `g` that takes that variable as its variable argument `n`. -/
def resultFlow (cs : Array Construct) (f g : IR.FunId) (n : Nat) : Bool :=
  (positionsFrom cs 0).any fun i =>
    match cs[i]? with
    | some (.call fi _ (some bound)) =>
      fi == f && (positionsFrom cs (i + 1)).any (fun j =>
        match cs[j]? with
        | some (.call gj args _) => gj == g && argAt args n == some bound
        | _ => false)
    | _ => false

/-- Whether a path holds a call to `f` bound to a variable, then a projection of
that variable's field `field` into another variable, then a call to `g` that
takes the projected variable as its variable argument `n`, each step after the
one before it. -/
def projectionFlow (cs : Array Construct) (f g : IR.FunId) (field n : Nat) : Bool :=
  (positionsFrom cs 0).any fun i =>
    match cs[i]? with
    | some (.call fi _ (some src)) =>
      fi == f && (positionsFrom cs (i + 1)).any (fun j =>
        match cs[j]? with
        | some (.proj k x bound) =>
          k == field && x == src && (positionsFrom cs (j + 1)).any (fun l =>
            match cs[l]? with
            | some (.call gl args _) => gl == g && argAt args n == some bound
            | _ => false)
        | _ => false)
    | _ => false

/-- Whether a path holds a call to `f` and, later on the same path, a call to `g`
that takes the variable of `f`'s variable argument `m` as its variable argument
`n`. -/
def argFlow (cs : Array Construct) (f g : IR.FunId) (m n : Nat) : Bool :=
  (positionsFrom cs 0).any fun i =>
    match cs[i]? with
    | some (.call fi argsi _) =>
      fi == f && (positionsFrom cs (i + 1)).any (fun j =>
        match cs[j]? with
        | some (.call gj argsj _) =>
          gj == g &&
            (match argAt argsi m with
             | some x => argAt argsj n == some x
             | none => false)
        | _ => false)
    | _ => false

/-- A construct as the IR prints it, so that the operands a flow requirement
binds and the reference-count steps beside them are visible in the survey. -/
def Construct.render : Construct → String
  | .call f args bound? =>
    let applied := String.intercalate " " (f.toString :: args.toList.map fun a =>
      match a with | .var x => toString x | .erased => "◾")
    match bound? with
    | some x => s!"{x} := {applied}"
    | none => applied
  | .proj field x bound => s!"{bound} := proj[{field}] {x}"
  | .testShared x => s!"isShared {x}"
  | .incRef x => s!"inc {x}"
  | .decRef x => s!"dec {x}"
  | .cellSet x i => s!"set {x}[{i}]"

/-- A path, as the survey prints it. -/
def renderConstructs (cs : Array Construct) : String :=
  s!"[{String.intercalate ", " (cs.toList.map Construct.render)}]"

/-- The body of the alternative for the constructor `ctor`, in the first `case`
of `b` that has one, searching a join point's body before the body that
declares it and an alternative's body after the alternatives of the `case`. -/
partial def altBody? (b : IR.FnBody) (ctor : Name) : Option IR.FnBody :=
  match b with
  | .vdecl _ _ _ rest => altBody? rest ctor
  | .jdecl _ _ value rest => (altBody? value ctor) <|> (altBody? rest ctor)
  | .set _ _ _ rest => altBody? rest ctor
  | .setTag _ _ rest => altBody? rest ctor
  | .uset _ _ _ rest => altBody? rest ctor
  | .sset _ _ _ _ _ rest => altBody? rest ctor
  | .inc _ _ _ _ rest => altBody? rest ctor
  | .dec _ _ _ _ rest => altBody? rest ctor
  | .del _ rest => altBody? rest ctor
  | .case _ _ _ alts =>
    (alts.findSome? fun a => match a with
      | .ctor info body => if info.name == ctor then some body else none
      | .default _ => none) <|>
    (alts.findSome? fun a => altBody? a.body ctor)
  | .ret _ => none
  | .jmp _ _ => none
  | .unreachable => none

/-! ## The declarations the check reads

Each entry is a name the environment is asked for. The path write of
`Layout5.setLeaf` runs in `setAt`, whose array case runs `takeOut`, so those are
the three declarations the layout side is read at, beside the bounds walk
`inBounds`, which is the same module's borrowed read. The structured side is the
executor's program interpreter `execP` and its reader `execR`. -/

/-- The private name the compiler mangles a `private` declaration into, for the
module that declares it. -/
def privateName (mod decl : Name) : Name := mkPrivateNameCore mod decl

/-- The arity-reduced variant a declaration's own entry calls. -/
def reducedName (n : Name) : Name := n ++ `_redArg

/-- The module that holds the path write. -/
def layout5 : Name := `Scidonia.FracPerm.StateVar.Layout5

/-- The module that holds the structured executor. -/
def executor : Name := `Scidonia.FracPerm.Structured.Executor

/-- The array step of a path. -/
def pathIndex : Name := `Scidonia.FracPerm.StateVar.Layout5.Path.index

/-- The `set` case of a program tree. -/
def pTreeSet : Name := `Scidonia.FracPerm.Structured.PTree.set

/-- The entry point of the path write, whose body is the reduced call below. -/
def setLeafEntry : Name := ``Scidonia.FracPerm.StateVar.Layout5.setLeaf

/-- The write the path write runs. -/
def setLeaf : Name := reducedName setLeafEntry

/-- The fused path update. -/
def setAt : Name := reducedName (privateName layout5 `Scidonia.FracPerm.StateVar.Layout5.setAt)

/-- The bounds walk. -/
def inBounds : Name :=
  reducedName (privateName layout5 `Scidonia.FracPerm.StateVar.Layout5.inBounds)

/-- The owned element exchange. -/
def takeOut : Name :=
  reducedName (privateName layout5 `Scidonia.FracPerm.StateVar.Layout5.takeOut)

/-- The structured program interpreter. -/
def execP : Name :=
  reducedName (privateName executor `Scidonia.FracPerm.Structured.execP)

/-- The structured read interpreter. -/
def execR : Name :=
  reducedName (privateName executor `Scidonia.FracPerm.Structured.execR)

/-- The library's array check, as the interpreter calls it. -/
def checkArray : Name := reducedName ``Scidonia.FracPerm.assertExclusiveArrayImpl

/-- The library's focus check, as the path update calls it. -/
def checkFocus : Name := reducedName ``Scidonia.FracPerm.assertExclusiveImpl

/-! ## The survey

Each entry names the label the requirements below use, the declaration the
environment is asked for, the alternative to read when only one case is meant,
and whether the whole body is printed beside its constructs. -/

/-- One declaration the check reads. -/
structure Survey where
  /-- The label the survey and the requirements use. -/
  label : String
  /-- The declaration the environment is asked for. -/
  decl : Name
  /-- The constructor whose alternative is read, when only one case is meant. -/
  alt? : Option Name := none
  /-- Print the whole body, not only its constructs. -/
  verbose : Bool := false

/-- What one surveyed name contributes: the body itself, every construct the body
holds, and the constructs of each executing path through it. A requirement that
says what a body names reads `whole`; one that says what a path does reads
`paths`. -/
structure Reading where
  /-- The body the environment holds. -/
  body : IR.FnBody
  /-- Every construct the body holds, alternatives included. -/
  whole : Array Construct
  /-- The constructs of each executing path through the body. -/
  paths : Array (Array Construct)

/-- Whether a requirement is about a body as a whole or about one executing path
through it. The report prints this beside every requirement, so a membership
requirement is not read as a flow. -/
inductive Scope where
  /-- The body as a whole: every alternative it holds, in the order it holds
  them. Membership, not a flow. -/
  | wholeBody
  /-- One executing path: the calls that can occur together, in the order they
  occur. -/
  | onePath

/-- How a scope is named in the report. -/
def Scope.render : Scope → String
  | .wholeBody => "whole body"
  | .onePath => "one path"

/-- What a reading holds, for a requirement that failed over it: the constructs of
the body as a whole and of every path, so the path that lacks a call is visible
in the report. -/
def describeReading (r : Reading) : String :=
  s!"the body as a whole is {renderConstructs r.whole}, and its paths are \
     {String.intercalate "; " (r.paths.toList.map renderConstructs)}"

/-- The body the environment holds for `s`, at the alternative `s.alt?` when one
is named. -/
def Survey.body? (env : Environment) (s : Survey) : Option IR.FnBody :=
  match IR.findEnvDecl env s.decl with
  | some (.fdecl _ _ _ body _) =>
    match s.alt? with
    | some ctor => altBody? body ctor
    | none => some body
  | _ => none

/-- The line that names the entry and the name it was read at. -/
def Survey.header (s : Survey) : String :=
  let suffix := match s.alt? with | some ctor => s!" [{ctor}]" | none => ""
  s!"{s.label}: {s.decl}{suffix}"

/-- The survey entry: the constructs the body holds as a whole, one line per
executing path with the operands and the reference-count steps the requirement
binds, and the body itself where the entry asks for it. -/
def Survey.render (s : Survey) (read : Option Reading) : String :=
  match read with
  | none => s!"{s.header}\n  no IR body in the environment for this name"
  | some r =>
    let pathLines := r.paths.toList.mapIdx fun i path =>
      s!"  path {i + 1} of {r.paths.size}, in the order it executes: {renderConstructs path}"
    let lines := #[s.header,
      s!"  the body as a whole, in the order it holds them: {renderConstructs r.whole}",
      s!"  executing paths: {r.paths.size}"] ++ pathLines.toArray
    let lines := if s.verbose then lines.push (toString r.body) else lines
    String.intercalate "\n" lines.toList

/-- The declarations the survey reads, in the order it reports them. -/
def survey : Array Survey := #[
  { label := "Layout5.setLeaf, entry point", decl := setLeafEntry, verbose := true },
  { label := "Layout5.setLeaf", decl := setLeaf, verbose := true },
  { label := "Layout5.setAt", decl := setAt },
  { label := "Layout5.setAt, Path.index", decl := setAt, alt? := some pathIndex },
  { label := "Layout5.inBounds, Path.index", decl := inBounds, alt? := some pathIndex },
  { label := "Layout5.takeOut", decl := takeOut },
  { label := "Structured.execP", decl := execP },
  { label := "Structured.execP, PTree.set", decl := execP, alt? := some pTreeSet, verbose := true },
  { label := "Structured.execR", decl := execR } ]

/-! ## The requirements

Each requirement is read off one surveyed body. Every requirement that a body
does *not* name a construct stands beside a control: a requirement that the same
test finds that construct in a body of the same run, so a test that matches
nothing fails the build rather than passing quietly. -/

/-- A shape requirement over one surveyed body. -/
structure Requirement where
  /-- The label of the survey entry it reads. -/
  label : String
  /-- Whether the body as a whole is read, or one executing path through it. -/
  scope : Scope
  /-- What is required, phrased for the report. -/
  what : String
  /-- The test over that entry's reading. -/
  holds : Reading → Bool

/-- The requirements, in the order they are reported. A requirement whose meaning
is a sequence or a flow reads one executing path, so the calls it sees can occur
together; a requirement about what a body names reads the body as a whole, which
the report says beside it.

The operand positions the flow requirements bind are the callees' own: the
take-out's pair puts the array it leaves at position 0 and the extracted element
at position 1, and the exclusivity checks take their site string at position 0
and the object they check at position 1, whether or not the application erases
the element type in front of them. -/
def requirements : Array Requirement := #[
  { label := "Layout5.setLeaf",
    scope := .wholeBody,
    what := "the body as a whole names `isShared`, the test a rebuild of the whole value makes",
    holds := fun r => namesShared r.whole },
  { label := "Layout5.setLeaf",
    scope := .wholeBody,
    what := "the body as a whole writes a constructor cell with `set`, the rebuilt value's cell",
    holds := fun r => writesCell r.whole },
  { label := "Layout5.setAt",
    scope := .wholeBody,
    what := "the body as a whole names `isShared`, the test a rebuild of a struct cell makes",
    holds := fun r => namesShared r.whole },
  { label := "Layout5.setAt",
    scope := .wholeBody,
    what := "the body as a whole writes a constructor cell with `set`",
    holds := fun r => writesCell r.whole },
  { label := "Layout5.setAt, Path.index",
    scope := .onePath,
    what := "on one path, the array check, the take-out, the focus check, the recursion \
      and `Array.set` occur in that order, the take-out's extracted focus — the second \
      component of the pair it returns — is the object the focus check is applied to, the \
      checked focus is the recursion's operand at position 2, and the placeholder write \
      takes the pair's first component as its operand at position 0, at the index the \
      take-out took the element from, its operand at position 1",
    holds := fun r => r.paths.any fun cs =>
      callsInOrder cs [checkArray, takeOut, checkFocus, setAt, `Array.set] &&
        projectionFlow cs takeOut checkFocus 1 1 &&
        resultFlow cs checkFocus setAt 2 &&
        projectionFlow cs takeOut `Array.set 0 0 &&
        argFlow cs takeOut `Array.set 1 1 },
  { label := "Layout5.setAt, Path.index",
    scope := .wholeBody,
    what := "the body as a whole does not name `Array.getInternalBorrowed`",
    holds := fun r => !namesCall r.whole `Array.getInternalBorrowed },
  { label := "Layout5.inBounds, Path.index",
    scope := .wholeBody,
    what := "the body as a whole names `Array.getInternalBorrowed`, the control for the requirement above",
    holds := fun r => namesCall r.whole `Array.getInternalBorrowed },
  { label := "Layout5.takeOut",
    scope := .wholeBody,
    what := "the body as a whole names `Array.getInternal`, the owned element read of a take-out",
    holds := fun r => namesCall r.whole `Array.getInternal },
  { label := "Layout5.takeOut",
    scope := .wholeBody,
    what := "the body as a whole names `Array.set`, the placeholder write beside it",
    holds := fun r => namesCall r.whole `Array.set },
  { label := "Structured.execP, PTree.set",
    scope := .wholeBody,
    what := "the body as a whole names `Array.set!`, the structured write",
    holds := fun r => namesCall r.whole `Array.set! },
  { label := "Structured.execP, PTree.set",
    scope := .onePath,
    what := "on one path, the variable the array check is bound to is the array operand of \
      `Array.set!`, its operand at position 0, so a check whose result is discarded, or a \
      write whose array operand is bound to anything else, does not satisfy it",
    holds := fun r => r.paths.any fun cs => resultFlow cs checkArray `Array.set! 0 },
  { label := "Structured.execP, PTree.set",
    scope := .wholeBody,
    what := "the body as a whole does not name `Array.getInternalBorrowed`",
    holds := fun r => !namesCall r.whole `Array.getInternalBorrowed },
  { label := "Structured.execR",
    scope := .wholeBody,
    what := "the body as a whole names `Array.getInternalBorrowed`, the control for the requirement above",
    holds := fun r => namesCall r.whole `Array.getInternalBorrowed },
  { label := "Structured.execP, PTree.set",
    scope := .wholeBody,
    what := "the body as a whole does not name `Array.getInternal` or `Array.set`, whose controls are the take-out requirements above",
    holds := fun r =>
      (!namesCall r.whole `Array.getInternal) && (!namesCall r.whole `Array.set) } ]

/-- The survey of the environment and the requirements read off it: the report
the command prints, and the failures it throws on. Every requirement is reported
with its outcome, so a control that finds its construct is as visible as a
requirement that does not. A surveyed name the environment holds no body for is
one of the failures, so the check cannot pass by reading nothing. -/
def irShapeReport (env : Environment) : String × Array String := Id.run do
  let reads : Array (Survey × Option Reading) :=
    survey.map fun s =>
      (s, (s.body? env).map fun body =>
        { body := body, whole := constructsOf body, paths := pathsOf body })
  let mut surveyLines : Array String := #[]
  for (s, read) in reads do
    surveyLines := surveyLines.push (s.render read)
  let mut requirementLines : Array String := #[]
  let mut failures : Array String := #[]
  for r in requirements do
    let entry := reads.findSome? fun (s, read) => if s.label == r.label then some read else none
    let holds : Except String Unit := match entry with
      | none => .error "no survey entry is read under this label"
      | some none => .error "this name has no IR body"
      | some (some read) =>
        if r.holds read then .ok () else .error (describeReading read)
    match holds with
    | .ok () =>
      requirementLines :=
        requirementLines.push s!"  ok      [{r.scope.render}] {r.label}: {r.what}"
    | .error why =>
      requirementLines :=
        requirementLines.push s!"  FAILED  [{r.scope.render}] {r.label}: {r.what}"
      failures := failures.push s!"[{r.scope.render}] {r.label}: {r.what} — {why}"
  let report := String.intercalate "\n"
    (surveyLines.toList ++ ["IR shape requirements"] ++ requirementLines.toList)
  return (report, failures)

run_cmd do
  let env : Environment ← liftCoreM getEnv
  let (report, failures) := irShapeReport env
  IO.println report
  unless failures.isEmpty do
    throwError s!"the IR shape check failed:\n{String.intercalate "\n" failures.toList}"

end ScidoniaTest.IRShape
