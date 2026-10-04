---
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: bridged
---

# Relative homology commutes with exact coproducts

Assume the coefficient category has exact coproducts of the size of the index
type, expressed by Mathlib's `AB4OfSize` interface. Construct the natural
isomorphism

`∐ i, H_n(P_i;R) ≅ H_n(Σ P_i;R)`

whose forward map restricts on each coproduct summand to the relative-homology
map induced by the corresponding sigma inclusion. The main artifact is
`Hatcher.Relative.relativeHomologySigmaIso`.

Derive the result from `relativeChainComplexSigmaIso` and exactness of the
coproduct functor. Do not state this under only `[Abelian C]` and
`[HasCoproducts C]`: infinite coproducts need not preserve homology in an
arbitrary abelian category. Mathlib supplies the required AB4 instance for
`AddCommGrpCat`, which covers Hatcher's integral statement.

## Depends on

- [Relative singular chains commute with topological coproducts](singular-relative-chains-coproduct.md)

## Sources

- [Hatcher §2.1, direct-sum formula in Corollary 2.25, printed page 126](../../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../../sources/post-excision-applications-implementation.md)
