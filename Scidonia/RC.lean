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
reaches.
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
