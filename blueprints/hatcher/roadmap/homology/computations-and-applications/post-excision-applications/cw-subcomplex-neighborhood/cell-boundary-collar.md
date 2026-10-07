---
article_id: af_4287a147c2d2150daf5a2475
source_units: [appendix-proposition-a-5]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.ClassicalCW.cellBoundaryCollarDeformation
---

# The radial collar of a cell boundary

For the closed sup-norm ball used by a classical CW characteristic map,
construct the fixed-width radial collar of its boundary and a deformation
that slides this collar outward onto the boundary. The deformation must be
stationary on the boundary and respect the radial coordinate. In the global
time schedule it is the identity before its assigned interval and remains
constant at its retracted endpoint after that interval.

Supporting declarations record the collar set, its openness relative to the
closed cell, its radial retraction, and endpoint and boundary-fixing
formulas.

This is the cellwise construction used in Hatcher's proof of Proposition
A.5; it does not yet descend through characteristic maps or assemble a global
CW homotopy.

## Depends on

None beyond Mathlib's classical sup-norm cell model.

## Sources

- [Hatcher, construction of `Nε(A)` and Appendix Proposition A.5, printed pages 522–523](../../../../../sources/hatcher-appendix-a5.md)
- [CW-subcomplex neighborhood implementation specification](../../../../../sources/cw-subcomplex-neighborhood-implementation.md)
