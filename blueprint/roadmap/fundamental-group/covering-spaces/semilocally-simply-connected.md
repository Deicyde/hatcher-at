---
declaration: class
origin: cited
---

# Semilocally simply-connected spaces

Define `Hatcher.SemilocallySimplyConnectedSpace X` to mean that every
`x : X` has an open neighborhood `U` for which the inclusion-induced map

`π₁(U,x) →* π₁(X,x)`

is trivial. The definition should use the subtype basepoint explicitly and
include a lemma transporting the property between basepoints inside a
path-connected `U`.

This is Hatcher's unnumbered definition on page 63. It is weaker than local
simple connectivity, and it must not be replaced by local contractibility.
The pinned Mathlib has no corresponding class.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.3, semilocal simple connectivity on page 63](../../../sources/hatcher-1-3.md)
