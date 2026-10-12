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

`constructsOf` records, in the order a body holds them, the three things the
requirements below ask about: the functions a body calls, the `isShared` tests it
makes, and the cells it writes with `set`. `altBody?` reaches one alternative of
a `case` — the array step of a path recursion, or the `set` case of the executor
— by the constructor name it matches. -/

/-- One construct of a body's IR. -/
inductive Construct where
  /-- A full or partial application of a function. -/
  | call (f : IR.FunId)
  /-- A test of whether an object is shared. -/
  | testShared (x : IR.VarId)
  /-- A write of a constructor object's cell. -/
  | cellSet (x : IR.VarId) (i : Nat)
  deriving BEq

/-- The constructs an expression holds. -/
def constructsOfExpr (e : IR.Expr) : Array Construct :=
  match e with
  | .fap f _ => #[.call f]
  | .pap f _ => #[.call f]
  | .isShared x => #[.testShared x]
  | _ => #[]

/-- The constructs a body holds, in the order the body holds them: a join point's
own body first, then the body into which it was declared. -/
partial def constructsOf (b : IR.FnBody) : Array Construct :=
  match b with
  | .vdecl _ _ e rest => constructsOfExpr e ++ constructsOf rest
  | .jdecl _ _ value rest => constructsOf value ++ constructsOf rest
  | .set x i _ rest => #[.cellSet x i] ++ constructsOf rest
  | .setTag _ _ rest => constructsOf rest
  | .uset _ _ _ rest => constructsOf rest
  | .sset _ _ _ _ _ rest => constructsOf rest
  | .inc _ _ _ _ rest => constructsOf rest
  | .dec _ _ _ _ rest => constructsOf rest
  | .del _ rest => constructsOf rest
  | .case _ _ _ alts => alts.foldl (fun acc a => acc ++ constructsOf a.body) #[]
  | .ret _ => #[]
  | .jmp _ _ => #[]
  | .unreachable => #[]

/-- The calls a body makes, in order, repeats included. -/
def callsOf (cs : Array Construct) : Array IR.FunId :=
  cs.filterMap fun c => match c with | .call f => some f | _ => none

/-- The objects a body tests for sharing. -/
def sharedOf (cs : Array Construct) : Array IR.VarId :=
  cs.filterMap fun c => match c with | .testShared x => some x | _ => none

/-- The cells a body writes. -/
def cellWritesOf (cs : Array Construct) : Array String :=
  cs.filterMap fun c => match c with | .cellSet x i => some s!"{x}[{i}]" | _ => none

/-- Whether a body names `f`. -/
def namesCall (cs : Array Construct) (f : IR.FunId) : Bool := cs.any (· == .call f)

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

/-- The survey entry: the constructs of the body it read, and the body itself
where the entry asks for it. -/
def Survey.render (s : Survey) (read : Option (IR.FnBody × Array Construct)) : String :=
  match read with
  | none => s!"{s.header}\n  no IR body in the environment for this name"
  | some (body, cs) =>
    let lines := #[s.header,
      s!"  calls, in order: {(callsOf cs).toList}",
      s!"  isShared: {(sharedOf cs).toList}",
      s!"  cell writes: {(cellWritesOf cs).toList}"]
    let lines := if s.verbose then lines.push (toString body) else lines
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
  /-- What is required, phrased for the report. -/
  what : String
  /-- The test over that entry's constructs. -/
  holds : Array Construct → Bool

/-- The requirements, in the order they are reported. -/
def requirements : Array Requirement := #[
  { label := "Layout5.setLeaf",
    what := "names `isShared`, the test a rebuild of the whole value makes",
    holds := fun cs => namesShared cs },
  { label := "Layout5.setLeaf",
    what := "writes a constructor cell with `set`, the rebuilt value's cell",
    holds := fun cs => writesCell cs },
  { label := "Layout5.setAt",
    what := "names `isShared`, the test a rebuild of a struct cell makes",
    holds := fun cs => namesShared cs },
  { label := "Layout5.setAt",
    what := "writes a constructor cell with `set`",
    holds := fun cs => writesCell cs },
  { label := "Layout5.setAt, Path.index",
    what := "names the array check, the take-out, the focus check, the recursion and `Array.set`, in that order",
    holds := fun cs => callsInOrder cs [checkArray, takeOut, checkFocus, setAt, `Array.set] },
  { label := "Layout5.setAt, Path.index",
    what := "does not name `Array.getInternalBorrowed`",
    holds := fun cs => !namesCall cs `Array.getInternalBorrowed },
  { label := "Layout5.inBounds, Path.index",
    what := "names `Array.getInternalBorrowed`, the control for the requirement above",
    holds := fun cs => namesCall cs `Array.getInternalBorrowed },
  { label := "Layout5.takeOut",
    what := "names `Array.getInternal`, the owned element read of a take-out",
    holds := fun cs => namesCall cs `Array.getInternal },
  { label := "Layout5.takeOut",
    what := "names `Array.set`, the placeholder write beside it",
    holds := fun cs => namesCall cs `Array.set },
  { label := "Structured.execP, PTree.set",
    what := "names `Array.set!`, the structured write",
    holds := fun cs => namesCall cs `Array.set! },
  { label := "Structured.execP, PTree.set",
    what := "names the array check before `Array.set!`",
    holds := fun cs => callsInOrder cs [checkArray, `Array.set!] },
  { label := "Structured.execP, PTree.set",
    what := "does not name `Array.getInternalBorrowed`",
    holds := fun cs => !namesCall cs `Array.getInternalBorrowed },
  { label := "Structured.execR",
    what := "names `Array.getInternalBorrowed`, the control for the requirement above",
    holds := fun cs => namesCall cs `Array.getInternalBorrowed },
  { label := "Structured.execP, PTree.set",
    what := "does not name `Array.getInternal` or `Array.set`, whose controls are the take-out requirements above",
    holds := fun cs =>
      (!namesCall cs `Array.getInternal) && (!namesCall cs `Array.set) } ]

/-- The survey of the environment and the requirements read off it: the report
the command prints, and the failures it throws on. Every requirement is reported
with its outcome, so a control that finds its construct is as visible as a
requirement that does not. A surveyed name the environment holds no body for is
one of the failures, so the check cannot pass by reading nothing. -/
def irShapeReport (env : Environment) : String × Array String := Id.run do
  let reads : Array (Survey × Option (IR.FnBody × Array Construct)) :=
    survey.map fun s => (s, (s.body? env).map (fun body => (body, constructsOf body)))
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
      | some (some (_, cs)) =>
        if r.holds cs then .ok ()
        else .error s!"the body's constructs are {(callsOf cs).toList} and its cells {(cellWritesOf cs).toList}"
    match holds with
    | .ok () =>
      requirementLines := requirementLines.push s!"  ok      {r.label}: {r.what}"
    | .error why =>
      requirementLines := requirementLines.push s!"  FAILED  {r.label}: {r.what}"
      failures := failures.push s!"{r.label}: {r.what} — {why}"
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
