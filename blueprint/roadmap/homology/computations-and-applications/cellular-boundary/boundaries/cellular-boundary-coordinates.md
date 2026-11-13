---
declaration: def
origin: bridged
article_id: af_9167e49074bca9673dfca34e
lean: Hatcher.ClassicalCW.cellularBoundaryCoordinates, Hatcher.ClassicalCW.cellularBoundaryCoordinates_reconstruct, Hatcher.ClassicalCW.cellularBoundaryCoordinates_eq_of_basisIso
statement: formalized
proof: formalized
---

# Coefficients of the actual cellular differential

For every classical CW complex and each differential Cₙ₊₁ → Cₙ, construct its integer coefficients in the existing characteristic-cell bases. A basis cell maps to its resulting finite-support coordinate family, and reconstruct the actual differential value from those coordinates. Include degree-zero targets and arbitrary cell sets.

## Proof sketch

Choose the inverse of the fixed free-cell isomorphism and apply it to the actual differential of a characteristic class. The prescribed images of all standard vectors make the coordinates independent of the isomorphism witness.

## Depends on

- [The cellular complex is formed from skeletal relative homology](../../cellular-homology/cellular-chain-complex.md)
- [Skeletal relative homology is concentrated in the cell dimension](../../cellular-homology/skeleton-relative-homology.md)

## Sources

- [Hatcher §2.2, printed pages 140–141](../../../../../sources/hatcher-2-2-cellular-boundary.md#higher-boundary-formula)
- [Project-authored cellular boundary specification](../../../../../sources/cellular-boundary-implementation.md)
