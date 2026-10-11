---
article_id: af_ea15ac26d6ba9e882549231f
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: bridged
---

# Deleted-pair homology is local on an open neighborhood

For `F : Set X`, write `Hatcher.Relative.deletedPair X F` for
`(X, X \ F)`. If `F` is closed, `W` is open, and `F ⊆ W`, define the canonical
pair morphism from the deleted pair inside `W` to `deletedPair X F`.

The main theorem
`Hatcher.Relative.deletedPairOpenNeighborhoodMap_isIso` says that this map
induces an isomorphism on relative homology in every degree. Include a
`T1Space` specialization for finite `F`, using that finite sets are closed.
For `F = {x}`, identify the map with the completed
`localHomologyOpenNeighborhoodMap`.

## Depends on

- [Relative singular chains and homology](../../simplicial-and-singular/relative-homology/relative-singular-homology.md)
- [Local homology is unchanged on an open neighborhood](../local-homology-and-dimension/local-homology-open-neighborhood.md)

## Proof depends on

- [Deleted-subset homology excision](../../simplicial-and-singular/relative-homology/small-chains-and-excision/deleted-subset-excision-homology-isomorphism.md)

## Sources

- [Hatcher §2.2, excision in the proof of Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
