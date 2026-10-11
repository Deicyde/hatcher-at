---
article_id: af_158175fa503c963a995517cb
source_units: [hatcher-2-2-local-degree]
declaration: def
origin: bridged
---

# Relative chains commute with coproducts of arbitrary pairs

For a family `P : ι → TopPair`, construct the chain-complex isomorphism

`∐ i, C_*(P i; R) ≅ C_*(sigmaPair P; R)`.

The main artifact is
`Hatcher.Relative.relativeChainComplexSigmaPairIso`. Its forward morphism
must restrict on each summand to the relative-chain map induced by
`sigmaPairι P i`.

Refactor the completed singular-simplex sigma argument and the cokernel
comparison used by `relativeChainComplexSigmaIso`; preserve that pointed
declaration as a compatibility specialization rather than maintaining a
second proof.

## Depends on

- [The coproduct of a family of topological pairs](sigma-topological-pair.md)
- [Relative singular chains and homology](../../simplicial-and-singular/relative-homology/relative-singular-homology.md)
- [Relative singular chains commute with topological coproducts](../post-excision-applications/singular-relative-chains-coproduct.md)

## Sources

- [Hatcher §2.2, direct-sum step in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
