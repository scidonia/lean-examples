# How a write works

## The write, end to end
- `setLeaf` asks `inBounds` whether the path addresses anything; if not, it returns the state and `false`.
- Otherwise it casts the observation to the focus type once, and hands it to the update.
- The update walks the path: a leaf is replaced; a struct cell is destructured and rebuilt from its updated component; an array element is taken out, ==checked for exclusive ownership==, updated and put back.

```the write, checked
import Scidonia.FracPerm
open Scidonia.FracPerm.StateVar Layout5

abbrev Pairs : Layout := .arr (.struct (.leaf .uint) (.leaf .uint))
def left : ObsPath Pairs := ⟨.index 3 (.left .here), .uint, rfl⟩
def sibling : ObsPath Pairs := ⟨.index 3 (.right .here), .uint, rfl⟩
def tooFar : ObsPath Pairs := ⟨.index 9 (.left .here), .uint, rfl⟩
def demo : State Pairs := #[(0, 0), (1, 1), (2, 2), (7, 9)]

#guard decide (read? left demo == some (.uint 7))
#guard decide ((setLeaf left (42 : UInt64) demo).2 == true)
#guard decide (read? left (setLeaf left (42 : UInt64) demo).1 == some (.uint 42))
#guard decide (read? sibling (setLeaf left (42 : UInt64) demo).1 == some (.uint 9))
#guard decide ((setLeaf tooFar (1 : UInt64) demo).2 == false)
#guard decide ((setLeaf tooFar (1 : UInt64) demo).1 == demo)
```

## The one question the compiler asks
- Every mutation site asks a single question: ==is this object's reference count exactly 1 here?==
- Count 1 → update in place. Count 2 or more → allocate a copy. A compile-time constant is a third case: its count is 0, it is never exclusive, and it always copies.
- So "do we get update semantics" is decided by what the compiler can prove about the count at that point — which is a *local, syntactic* fact, not something our types say.

## Twelve shapes, measured
- Each compiled and run on this toolchain, measuring the object's address before and after. (A scratch executable; the harness carries the cases that ship.)
- `a.set! i v` on an owned array → ==in place==
- the same array, with a live alias → copied
- `(a.set! i v, a.size)` — no alias, one extra use → copied
- `{ s with hits := s.hits + 1 }` → the struct cell is reused
- `({ s with log := s.log.set! 0 v }, s.log.size)` → struct reused, `log` copied
- `({ s with hits := s.hits + 1 }, true)` → the struct cell is reused
- `{ s with log := s.log.set! 0 v }` → `log` in place
- `a.modify i (fun inner => inner.set! j v)` → the inner array is in place
- `let inner := a[i]!; a.set! i (inner.set! j v)` → the inner array is copied
- updating with an alias to the struct live → copied
- `a.push v` with room to spare → in place; with no room → reallocated

## What the emitted code shows
- Three signals decide every case above:
  - `inc x` before a mutation — the value is used again in the same expression, or an alias is live. In `(a.set! i v, a.size)` the emitted code is `inc x_1; let x_5 := Array.set! ◾ x_1 …; let x_6 := Array.size ◾ x_1`.
  - `isShared` before a rebuild — the reset/reuse pass rewrites the *incoming* cell when it is exclusive: `lean_is_exclusive(x)` then `lean_ctor_set(x, 1, …)` and `return x`; the `reuseFailAlloc` branch beside it is the copy.
  - take-out versus a borrowed get — `Array.getInternal` with a placeholder `Array.set` (in place) against `Array.get!InternalBorrowed` followed by `inc` (copied).
- ==The last pair is the whole reason `takeOut` exists.== Identical intent, opposite outcome, decided by whether the element is taken out or merely borrowed.

## A normal update is not the copying case
- The reading-and-writing-in-one-expression shape is not what a write does here. `setLeaf` compiles to a bounds check and then the update, with ==no increment of the state at all==: `inBounds___redArg(path, s)` followed by `setAt___redArg(path, x, s)`.
- The reason is that the check returns a `Bool`: it retains nothing, so the state's uses are sequential and its last use is a move.
- And a client could not write the copying shape anyway: the client has no state, only commands — there is no value to write and read at once.

## Two traps, and the shapes that avoid them
- **The check and the pair.** The take-out returns an `(array, element)` pair. While that pair is live the element has two references, so the exclusivity check fires on a unique array. The fix is to destructure the pair before checking: the emitted code releases the pair, then checks the focus with one reference.
- **The cell that gets reused.** With the update returning `State d × Bool`, reset/reuse fired on the *transient* pair, so the struct actually stored was fresh — the address changed while the C looked like it contained reuse. The fix is the state-only recursion: `let (a, b) := s; (setAt q y a, b)`, whose result has the shape of the cell it came from, leaving exactly one candidate.
- Both were found by ==measuring addresses==, not by reading the source or the C.

## What is asserted, and what is trusted
- The harness asserts addresses: `layout5-unique` (the array and the written struct keep their addresses), `layout5-nest` (the focused inner array does), and the controls that must copy — `layout5-shared-copies`, `layout5-nest-aliased` — plus the checked children, which must abort naming the site.
- Checked mode is diagnostic: it neither proves nor enforces where it is off, and it rests on the runtime's exclusivity primitive.
- Nothing here is a theorem about the compiler. The logical half is proved: `setAt_spec` ties the executed update to the zipper, and the snapshot and frame theorems are stated over `setLeaf`.

## The rules
- You get an update in place when all of these hold:
  1. the object was allocated at run time;
  2. its count is 1 at the mutation — no alias, no projection held, and no second use of the same value in one expression;
  3. for a rebuild, the cell the pass reuses is the one stored (shaped so there is a single candidate);
  4. for a nested write, every node on the path is exclusive at the moment of the write — which is what the take-out and the focus check establish;
  5. the write is a fixed-size element write: ==growth is out of scope== and an append needs spare capacity.
- The two that our surface settles by *types* rather than by care: the write installs an observation (so no client alias can enter), and there is no growth operation.
