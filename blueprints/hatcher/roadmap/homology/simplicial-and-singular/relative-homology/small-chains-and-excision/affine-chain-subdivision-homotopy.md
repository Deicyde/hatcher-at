---
article_id: af_79821bb097f7e681e401770f
source_units: [hatcher-2-1-small-chains-excision]
declaration: def
origin: bridged
---

# Affine-chain subdivision is homotopic to the identity

For a convex real space `Y`, universes `w`, `v`, and `u`, an ambient category
`C : Type u` with `[Category.{v} C]`, `[Preadditive C]`,
`[HasCoproducts.{w} C]`, and a coefficient object `R : C`, construct the
barycentric subdivision endomorphism of the affine-simplex chain complex.
Construct its cone homotopy from the identity, naturally with respect to
affine maps.

The main artifact, intended as
`Hatcher.Excision.affineChainHomotopyIdSubdivision`, is this chain homotopy.
The subdivision map, cone operator, signed sum over permutation-indexed
subsimplices, and corresponding iterated formula are supporting declarations
in the same review unit. This is the categorical version of Hatcher's augmented
linear-chain construction on pages 121–122.

## Depends on

- [Affine barycentric subdivision is compatible with faces](affine-barycentric-subdivision.md)

## Sources

- [Hatcher §2.1, subdivision of linear chains, pages 121–122](../../../../../sources/hatcher-2-1.md)
- [Singular excision implementation specification](../../../../../sources/excision-implementation.md)
- [Riou's affine-chain implementation prior art](https://github.com/joelriou/excision/blob/8b56cd0c8e5f39a7c2f36418c80b298e469596a6/Excision/ConvexSpace/AffineChains.lean)
