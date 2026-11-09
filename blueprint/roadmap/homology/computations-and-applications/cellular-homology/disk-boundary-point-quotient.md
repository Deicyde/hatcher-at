---
article_id: af_8b76282ab7c960a7937a1a2a
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.ClassicalCW.diskBoundaryPointQuotientIsoSphere, Hatcher.ClassicalCW.standardDiskBoundaryPair, Hatcher.ClassicalCW.diskBoundaryPairIsoCone, Hatcher.ClassicalCW.diskBoundaryPointQuotientIsoSphere_hom, Hatcher.ClassicalCW.diskBoundaryPointQuotientIsoSphere_point, Hatcher.ClassicalCW.diskBoundaryPointQuotientIsoSphere_projection, Hatcher.ClassicalCW.diskBoundaryPointQuotientIsoSphere_cylinder, Hatcher.ClassicalCW.diskZeroPairIsoPointEmpty
---

# Collapsing a disk boundary gives the next sphere

For every positive disk dimension m, construct a homeomorphism
Dᵐ/∂Dᵐ ≃ Sᵐ for the standard disk and boundary inclusion. It sends the collapsed
boundary to the fixed suspension pole and records the quotient projection on
actual disk points. For dimension zero, identify the pair (D⁰,∅) with the
point paired with the empty space.

## Proof sketch

Transport the exact standard disk-boundary pair through the proved cone-disk
homeomorphism. The fixed cone-base quotient homeomorphism gives the sphere and
its collapsed-point equation. Keep the point-and-empty-pair calculation
separate in dimension zero.

## Depends on

- [Point quotient functor](../../simplicial-and-singular/relative-homology/good-pair-quotient/point-quotient-functor.md)

## Proof depends on

- [Cone disk homeomorphism](../../../fundamental-group/van-kampen/cell-attachment-support/cone-disk-homeomorphism.md)
- [Sphere cone geometry](../degree-realization-suspension/suspension/sphere-cone-geometry.md)
- [Sphere cone quotient homeomorphism](../degree-realization-suspension/suspension/sphere-cone-quotient-homeomorphism.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)
