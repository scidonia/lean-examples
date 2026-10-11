# Outlook

## What the models establish, and what they do not
- Proved: the permission discipline for any lawful type, detached reads in the modelled encoding, snapshots, frames, and the universe's laws for every non-recursive description.
- `LawfulStateVar` alone does not prevent leaks: an author-chosen encoding can hide an alias. The sealed class closes that hole by owning the encoding.
- Not proved: Lean's physical pointers. The library's own primitives are checked at run time by the `inplace` harness, and the compiler is trusted.
- Next: recursive layouts, user structures with a layout that names them, per-path fractional permissions, and a real mutable cell behind the sealed interface.
