---
article_id: af_1a9a1f72a7f37bbe2e0be027
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.ClassicalCW.skeletonHomologyVanishing, Hatcher.ClassicalCW.homologyVanishingOfSkeletonEq, Hatcher.ClassicalCW.homologyVanishingOfCellDimensionBound, Hatcher.ClassicalCW.finiteDimensionalHomologyVanishing
---

# Homology vanishes above a skeleton dimension

**Hatcher, Lemma 2.34(b).** For every classical CW complex X and k > n,
Hₖ(Xⁿ;ℤ) is zero. If Xⁿ = X, the same vanishing holds for X. In particular,
a finite-dimensional CW complex has zero homology above any genuine bound
on its cell dimensions. The number of cells in each dimension may be infinite.

## Proof sketch

Start from higher-degree vanishing of the discrete zero skeleton and
induct through skeleton attachments using the step stability theorem.
Extract a skeleton bound from the finite-dimensional CW structure for the
last consequence.

## Depends on

- [Singular homology](../../simplicial-and-singular/singular-homology.md)

## Proof depends on

- [Zero skeleton discrete](zero-skeleton-discrete.md)
- [Totally disconnected higher homology](../../simplicial-and-singular/totally-disconnected-higher-homology.md)
- [Skeleton step homology stability](skeleton-step-homology-stability.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)
