---
article_id: af_34d74c61b68ff963c2a00cc2
---

# Cellular homology through its singular comparison

Hatcher §2.2, printed pages 137–140, derives the relative homology of successive
skeleta, vanishing above their dimension, and stability of their inclusion
maps. The cellular complex uses those actual relative groups and the pair
connecting maps; its homology agrees with ordinary singular homology.

This milestone has 15 planned formalizable leaves. None is marked proved.
Every final statement covers arbitrary classical CW complexes, including
empty complexes, infinitely many cells and unbounded dimensions. Put X⁻¹ = ∅;
in implementation, strict skeleton indices avoid natural subtraction.

## Geometry and relative groups

- [The zero skeleton is the discrete space of its cells](zero-skeleton-discrete.md)
- [A nonempty CW subcomplex gives a good pair](nonempty-subcomplex-good-pair.md)
- [Collapsing a disk boundary gives the next sphere](disk-boundary-point-quotient.md)
- [A successive skeleton quotient is the wedge of its cells](skeleton-quotient-wedge.md)
- [Every pointed sphere is a good pair](sphere-point-good-pair.md)
- [The zero-skeleton pair has the free group on its vertices](zero-skeleton-relative-homology.md)
- [Positive-dimensional skeletal pairs have the cell basis](positive-skeleton-relative-homology.md)
- [Skeletal relative homology is concentrated in the cell dimension](skeleton-relative-homology.md)

## Skeleton stability and finite chains

- [One skeleton attachment changes homology only in adjacent degrees](skeleton-step-homology-stability.md)
- [Homology vanishes above a skeleton dimension](skeleton-homology-vanishing.md)
- [Higher finite skeleta preserve low-degree homology](finite-stage-homology-stability.md)
- [Finite families of singular chains lift to one skeleton](singular-chains-bounded-skeleton.md)
- [The skeleton inclusion preserves homology below its dimension](skeleton-to-space-homology-stability.md)

## Cellular complex and comparison

- [The cellular complex is formed from skeletal relative homology](cellular-chain-complex.md)
- [Cellular homology agrees with singular homology](cellular-homology-comparison.md)

## Source boundary

The selected passage starts at Cellular Homology and ends with the proof of
Theorem 2.35. Its immediate applications, attaching-map degree formula,
Euler characteristic, later Mayer–Vietoris results and general coefficients
remain queued. Naturality for filtration-preserving maps and cellular
approximation require a later API pass.

## Sources

- [Hatcher §2.2 cellular homology](../../../../sources/hatcher-2-2-cellular.md)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)
