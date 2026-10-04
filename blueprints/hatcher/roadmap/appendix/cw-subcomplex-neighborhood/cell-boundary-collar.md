---
source_units: [appendix-proposition-a-5]
declaration: def
origin: bridged
---

# The radial collar of a cell boundary

For the closed sup-norm ball used by a classical CW characteristic map,
construct the fixed-width radial collar of its boundary and a deformation
that slides this collar outward onto the boundary. The deformation must be
stationary on the boundary, respect the radial coordinate, and agree with the
identity outside the time interval assigned to its cell dimension.

The main artifact is
`Hatcher.ClassicalCW.cellBoundaryCollarDeformation`. Supporting declarations
record the collar set, its openness relative to the closed cell, its radial
retraction, and endpoint and boundary-fixing formulas.

This is the cellwise construction used in Hatcher's proof of Proposition
A.5; it does not yet descend through characteristic maps or assemble a global
CW homotopy.

## Depends on

None beyond Mathlib's classical sup-norm cell model.

## Sources

- [Hatcher, construction of `Nε(A)` and Appendix Proposition A.5, printed pages 522–523](../../../sources/hatcher.md)
- [CW-subcomplex neighborhood implementation specification](../../../sources/cw-subcomplex-neighborhood-implementation.md)
