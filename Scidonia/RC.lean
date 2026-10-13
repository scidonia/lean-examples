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
-/
import Scidonia.RC.Syntax
import Scidonia.RC.Pure
import Scidonia.RC.Lower
import Scidonia.RC.Target
import Scidonia.RC.Ownership
import Scidonia.RC.Discipline
import Scidonia.RC.Typing
import Scidonia.RC.Correspondence
