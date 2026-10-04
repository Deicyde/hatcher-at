---
article_id: af_7e0d8531ee8d17dae6a2fb88
source_units: [appendix-proposition-a-5]
declaration: def
origin: background
statement: formalized
lean: Hatcher.ClassicalCW.Subcomplex.inter
---

# Intersections of CW subcomplexes

For two `CWComplex.Subcomplex C` objects, construct the subcomplex whose cells
are those belonging to both inputs and whose carrier is their set-theoretic
intersection. Expose the coercion formula

`↑(Hatcher.ClassicalCW.Subcomplex.inter A B) =`
`  (A : Set X) ∩ (B : Set X)`

and the corresponding cell-index formula. The main artifact is
`Hatcher.ClassicalCW.Subcomplex.inter`.

This is topology-neutral infrastructure for the identity
`N(A) ∩ N(B) = N(A ∩ B)` following Hatcher's Proposition A.5. The pinned
Mathlib revision has a `CWComplex.Subcomplex` structure but no intersection
or lattice operation on it.

## Depends on

None beyond Mathlib's classical CW-complex API.

## Sources

- [Hatcher, Appendix Proposition A.5 and the following intersection observation, printed page 523](../../../../../sources/hatcher-appendix-a5.md)
- [CW-subcomplex neighborhood implementation specification](../../../../../sources/cw-subcomplex-neighborhood-implementation.md)
