---
article_id: af_5f0a0a354967820017e486a7
source_units: [appendix-proposition-a-5]
declaration: structure
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.ClassicalCW.RegularNeighborhoodSystem
---

# A common regular-neighborhood system for subcomplexes

For a classical CW complex `C`, construct one fixed-width regular-neighborhood
assignment `N` for all `CWComplex.Subcomplex C`. Package the facts that

- `N A` is open in the ambient CW complex;
- the carrier of `A` lies in `N A`, hence in its interior; and
- `N (A.inter B) = N A ∩ N B`.

The main artifact is
`Hatcher.ClassicalCW.RegularNeighborhoodSystem`. It uses the same collar
width, chosen once with `0 < ε < 1`, in every occurrence of `N`; independently
chosen neighborhoods would not support the required intersection identity.

This node constructs the neighborhoods and their point-set identities. The
global deformation retraction is the next node.

## Depends on

- [Intersections of CW subcomplexes](subcomplex-intersection.md)
- [The radial collar of a cell boundary](cell-boundary-collar.md)

## Sources

- [Hatcher, construction of `Nε(A)` and Appendix Proposition A.5, printed pages 522–523](../../../../../sources/hatcher-appendix-a5.md)
- [CW-subcomplex neighborhood implementation specification](../../../../../sources/cw-subcomplex-neighborhood-implementation.md)
