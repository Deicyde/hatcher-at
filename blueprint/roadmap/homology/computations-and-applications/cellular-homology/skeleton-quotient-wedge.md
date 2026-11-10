---
article_id: af_014295821647fd8a388f2ad4
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.ClassicalCW.skeletonPointQuotientIsoWedge, Hatcher.ClassicalCW.skeletalStagePair, Hatcher.ClassicalCW.skeletalStageCellPairMap, Hatcher.ClassicalCW.skeletonPointQuotientIsoWedge_point, Hatcher.ClassicalCW.skeletonPointQuotientIsoWedge_cell, Hatcher.ClassicalCW.skeletonPointQuotientIsoWedge_pairMap, Hatcher.ClassicalCW.skeletonPointQuotientIsoWedge_inv_inclusion
---

# A successive skeleton quotient is the wedge of its cells

For every n > 0 and classical CW complex X, construct
Xⁿ/Xⁿ⁻¹ ≃ ⋁ᵢ Sⁿ, indexed by the actual n-cells of X and using the weak wedge
topology. The quotient point goes to the common wedge point. On each actual
characteristic disk, the homeomorphism is the boundary-collapse map followed
by that cell’s wedge inclusion. No finite-cell hypothesis is imposed.

## Proof sketch

Descend maps in both directions through the successor-skeleton quotient,
the boundary-collapse sphere models and the pointed-wedge universal property.
Check both composites on the old skeleton and every characteristic disk.
Use the quotient coproduct topology for an infinite cell family.

## Depends on

- [Point quotient functor](../../simplicial-and-singular/relative-homology/good-pair-quotient/point-quotient-functor.md)
- [Disk boundary point quotient](disk-boundary-point-quotient.md)

## Proof depends on

- [Classical and standard cells have isomorphic attaching arrows](../../../appendix/classical-cw-bridge/classical-cell-arrow-iso.md)
- [Successor skeleton quotient](../../../appendix/classical-cw-bridge/successor-skeleton-quotient.md)
- [Pointed wedge point quotient](../post-excision-applications/pointed-wedge-point-quotient.md)
- [Pointed wedge universal property](../../../fundamental-group/van-kampen/presentation-complex/pointed-wedge-universal-property.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)
