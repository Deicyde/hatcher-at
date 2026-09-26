---
article_id: af_9cc2a0377fff8b1774bfdf1f
source_units: [hatcher-2-1-small-chains-excision]
declaration: theorem
origin: cited
---

# Barycentric subdivision contracts simplex diameter

For an affine `n`-simplex `s` in a real normed space and any choice `σ` of
`k` successive barycentric subsimplices, the main theorem, intended as
`Hatcher.Excision.affineSubdivisionIter_diameter_le`, gives the bound

`diam (sdIter s σ) ≤ (n / (n + 1))^k · diam s`.

In particular, when `n > 0`, repeated subdivision makes every resulting
simplex arbitrarily small. The proof packages Hatcher's estimate from the
barycenter of a simplex to its vertices and iterates it uniformly over all
permutation-indexed subsimplices.

## Depends on

- [Affine barycentric subdivision is compatible with faces](affine-barycentric-subdivision.md)

## Sources

- [Hatcher §2.1, subdivision diameter estimate, pages 120–121](../../../../../sources/hatcher-2-1.md)
- [Singular excision implementation specification](../../../../../sources/excision-implementation.md)
- [Riou's diameter implementation prior art](https://github.com/joelriou/excision/blob/8b56cd0c8e5f39a7c2f36418c80b298e469596a6/Excision/ConvexSpace/Diameter.lean)
