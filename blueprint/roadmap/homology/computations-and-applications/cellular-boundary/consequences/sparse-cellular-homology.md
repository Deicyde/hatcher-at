---
declaration: theorem
origin: cited
article_id: af_b823d91d6171945253f9061e
lean: Hatcher.ClassicalCW.homologyCellBasisOfSparseCells
statement: formalized
proof: formalized
---

# Gaps between cell dimensions give the cell basis in homology

For every classical CW complex X with no adjacent occupied cell dimensions and every n ∈ ℕ, construct Hₙ(X;ℤ) as the free abelian group on the actual n-cells. Preserve those cell generators through the cellular/singular comparison. Include arbitrary cell sets, disconnected spaces and empty complexes.

## Proof sketch

With both neighboring differentials zero, cellular homology is the actual degree-n chain group. Transport its fixed cell basis by the completed comparison.

## Depends on

- [Singular homology](../../../simplicial-and-singular/singular-homology.md)

## Proof depends on

- [Gaps between cell dimensions force zero cellular differentials](sparse-cellular-differentials.md)
- [Skeletal relative homology is concentrated in the cell dimension](../../cellular-homology/skeleton-relative-homology.md)
- [Cellular homology agrees with singular homology](../../cellular-homology/cellular-homology-comparison.md)

## Sources

- [Hatcher §2.2, printed pages 140–141](../../../../../sources/hatcher-2-2-cellular-boundary.md#immediate-applications)
- [Project-authored cellular boundary specification](../../../../../sources/cellular-boundary-implementation.md)
