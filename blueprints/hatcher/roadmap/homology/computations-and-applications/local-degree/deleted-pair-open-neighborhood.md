---
article_id: af_ea15ac26d6ba9e882549231f
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: bridged
---

# Deleted-pair homology is local on an open neighborhood

For `F : Set X`, write `Hatcher.Relative.deletedPair X F` for
`(X, X \ F)` and define
`Hatcher.Relative.deletedPairWithin F W` as the pair inside `W` obtained by
deleting the preimage of `F`, represented as
`TopPair.ofSubset (Subtype.val ⁻¹' Fᶜ)`. If `F` is closed, `W` is open, and
`F ⊆ W`,
define the canonical morphism
`Hatcher.Relative.deletedPairOpenNeighborhoodPairHom F W` and its induced
homology map `Hatcher.Relative.deletedPairOpenNeighborhoodMap F W R n`.

The main theorem
`Hatcher.Relative.deletedPairOpenNeighborhoodMap_isIso` says that this map
induces an isomorphism on relative homology in every degree. Include a named
`deletedPairOpenNeighborhoodMap_isIso_of_finite` specialization in a
`T1Space`, using that finite sets are closed. Publish ambient and
proof-term-insensitive subspace component formulas for the pair map. No
nonemptiness hypothesis is permitted; in particular `F = ∅` remains valid.

For `F = {x}`, construct the canonical source-pair isomorphism from the
punctured pair of `W` to `deletedPairWithin {x} W`. Name the induced homology
isomorphism and prove at pair and homology level that its forward map followed
by the deleted-pair neighborhood map is the completed
`localHomologyOpenNeighborhoodMap`; do not claim a generally ill-typed literal
equality between their source objects.

## Depends on

- [Relative singular chains and homology](../../simplicial-and-singular/relative-homology/relative-singular-homology.md)
- [Local homology is unchanged on an open neighborhood](../local-homology-and-dimension/local-homology-open-neighborhood.md)

## Proof depends on

- [Binary-cover excision induces a homology isomorphism](../../simplicial-and-singular/relative-homology/small-chains-and-excision/binary-cover-excision-homology-isomorphism.md)

## Sources

- [Hatcher §2.2, excision in the proof of Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
