---
article_id: af_96911f811174cc9ed741c8af
source_units: [hatcher-1-3-selected-spine]
declaration: class
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.SemilocallySimplyConnectedSpace
---

# Semilocally simply-connected spaces

Define `Hatcher.SemilocallySimplyConnectedSpace X` to mean that every
`x : X` has an open neighborhood `U` for which the inclusion-induced map

`π₁(U,x) →* π₁(X,x)`

is trivial. The definition should use the subtype basepoint explicitly and
include a lemma transporting the property between basepoints inside a
path-connected `U`.

Formalized as `Hatcher.SemilocallySimplyConnectedSpace` in
`Hatcher/Covering/SemilocallySimplyConnected.lean`. The accompanying theorem
`Hatcher.trivial_fundamentalGroupMap_of_isPathConnected` proves the requested
basepoint independence inside a path-connected subspace.

This is Hatcher's unnumbered definition on page 63. It is weaker than local
simple connectivity, and it must not be replaced by local contractibility.
The pinned Mathlib has no corresponding class.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.3, semilocal simple connectivity on page 63](../../../../sources/hatcher-1-3.md)
