---
article_id: af_1bb146350ccc1bbd8409054f
source_units: [hatcher-2-1-small-chains-excision]
declaration: def
origin: bridged
---

# Singular-chain subdivision is naturally homotopic to the identity

For `X : TopCat.{w}`, `{C : Type u}`, `[Category.{v} C]`, `[Preadditive C]`,
`[HasCoproducts.{w} C]`, and `R : C`, transfer affine barycentric subdivision
of the standard simplex along every singular simplex. This gives a natural
chain endomorphism of `X`'s singular chain complex, together with all finite
iterates.

The main artifact, intended as
`Hatcher.Excision.singularChainHomotopyIdSubdivisionIter`, is a chain homotopy
from the identity to every iterated subdivision map. Supporting declarations
give the one-step homotopy, naturality under continuous maps, the signed
subsimplex formula, face compatibility, and the fact that every subdivided
simplex has image contained in the original simplex's image. These support
properties are what later make subdivision and its homotopies preserve
subspaces.

## Depends on

- [The singular chain complex](../../singular-chain-complex.md)
- [Affine barycentric subdivision is compatible with faces](affine-barycentric-subdivision.md)

## Proof depends on

- [Affine-chain subdivision is homotopic to the identity](affine-chain-subdivision-homotopy.md)

## Sources

- [Hatcher §2.1, subdivision of general chains, pages 122–123](../../../../../sources/hatcher-2-1.md)
- [Singular excision implementation specification](../../../../../sources/excision-implementation.md)
- [Riou's singular-subdivision implementation prior art](https://github.com/joelriou/excision/blob/8b56cd0c8e5f39a7c2f36418c80b298e469596a6/Excision/SingularHomology/Subdivision.lean)
