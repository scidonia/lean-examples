/-
The reference-counted slice: the calculus λPure, its reference-counted image
λRC, and the lowering between them.

`Scidonia.RC.Syntax` carries the one syntax the two calculi share and the
predicate that picks the source fragment out of it; `Scidonia.RC.Pure` carries
the source calculus's own reduction as a substitution semantics, its determinism
and the purity the fragment is named for; `Scidonia.RC.Lower` carries the graph
of the canonical syntax-directed strategy — the specialisation of the paper's
lowering this slice realises — and the totality and determinism that make the
strategy a function of the environments.

The slice's role in this repository is the write. A node's slot is replaced by a
value, and whether that replacement lands in the node or in a copy of it is
decided by the reference count of the node; λRC is the calculus where such a
count would be read, and the lowering is the step that puts the two resource
operations there. Nothing in this slice counts anything, so what is here is the
calculus a later module can put a count on: the source, the target, and which
target a source term becomes.

`Scidonia.RC.OwnershipTyped` is the ownership-typed fragment of the same
calculus, added beside these modules and changing none of them: an additional
`Prop` typing and an additional `Prop` ownership discipline over the existing
`Expr`, a quotation of the existing `Slot` as a λPure value, a private array
interpreter of the admitted fragment, and the agreement between that
interpreter's value and the value the copying reduction of the same term
reaches. The interpreter's own `IO` runner, `runFresh`, is available beside it
with its logical equation proved, and is not advertised as a supported execution
route.

`Scidonia.RC.TreeOwnership` extends the same calculus to a layout-indexed tree
state, again beside these modules and changing none of them: a quotation of a
`Layout5.State`, its navigation along a path, the detector that tells a leaf's
observation from a protected node, the per-node fractional account a spine of such
a tree is read and written under, the ownership relation over the same term with
its handle context and its refusals, the state-level replacement's own laws and
the conditional take-out transfer, and the private interpreter of the admitted
fragment with the agreement that its value is the value the copying reduction of
the same term reaches.
-/
import Scidonia.RC.Syntax
import Scidonia.RC.Pure
import Scidonia.RC.Lower
import Scidonia.RC.Target
import Scidonia.RC.Ownership
import Scidonia.RC.Discipline
import Scidonia.RC.Typing
import Scidonia.RC.Correspondence
import Scidonia.RC.Transfer
import Scidonia.RC.OwnershipTyped.Refinement
import Scidonia.RC.TreeOwnership.Quote
import Scidonia.RC.TreeOwnership.Spine
import Scidonia.RC.TreeOwnership.Judgement
import Scidonia.RC.TreeOwnership.Agreement
import Scidonia.RC.TreeOwnership.Executor
