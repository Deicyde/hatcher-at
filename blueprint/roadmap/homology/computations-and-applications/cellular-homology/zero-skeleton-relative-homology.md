---
article_id: af_70bc68672d03197021c19891
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.ClassicalCW.zeroSkeletonRelativeHomology, Hatcher.ClassicalCW.zeroSkeletonPair, Hatcher.ClassicalCW.zeroSkeletonOrdinaryRelativeChainIso, Hatcher.ClassicalCW.zeroSkeletonOrdinaryRelativeChainIso_hom, Hatcher.ClassicalCW.zeroSkeletonOrdinaryRelativeHomologyIso, Hatcher.ClassicalCW.zeroSkeletonOrdinaryRelativeHomologyIso_hom, Hatcher.ClassicalCW.zeroCellPoint, Hatcher.ClassicalCW.zeroCellPoint_val, Hatcher.ClassicalCW.zeroCellRelativeClass, Hatcher.ClassicalCW.zeroSkeletonRelativeHomologyIso, Hatcher.ClassicalCW.zeroSkeletonRelativeHomologyIso_inv_single, Hatcher.ClassicalCW.zeroSkeletonRelativeHomology_isZero
---

# The zero-skeleton pair has the free group on its vertices

For every classical CW complex X, ordinary integral relative homology of
(X⁰,∅) vanishes in every positive degree. In degree zero, construct its
isomorphism with the finite-support integer functions on the actual zero
cells, sending the standard vector at a vertex to its characteristic-point
class. Empty complexes are included.

## Proof sketch

Identify relative chains for the empty subspace with ordinary chains. Use
the discrete zero-skeleton model, the ordinary zeroth-homology calculation
and the exact coproduct of point generators. Do not replace ordinary degree
zero by reduced homology.

## Depends on

- [Relative singular homology](../../simplicial-and-singular/relative-homology/relative-singular-homology.md)

## Proof depends on

- [Zero skeleton discrete](zero-skeleton-discrete.md)
- [Totally disconnected higher homology](../../simplicial-and-singular/totally-disconnected-higher-homology.md)
- [Zeroth homology components](../../simplicial-and-singular/zeroth-homology-components.md)
- [Singular relative chains coproduct](../post-excision-applications/singular-relative-chains-coproduct.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)
