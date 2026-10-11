---
article_id: af_89e2481cf4df5cf4ef419a56
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: bridged
---

# The disjoint local pairs excise to the finite-puncture pair

For the chosen finite-fiber neighborhoods, compose the canonical pair
isomorphism from their sigma pair to the deleted union pair with the inclusion
of that open union into the sphere pair obtained by deleting the full fiber.
Call the resulting morphism
`Hatcher.Sphere.finitePuncturePairHom`.

Name the finite wrapper
`Hatcher.Sphere.finitePunctureSigmaPairIsoDeletedUnion`, whose target is
literally `deletedPairWithin (fiber f y) D.union`, and the direct local
inclusion `Hatcher.Sphere.finitePunctureNeighborhoodPairHom D i` into
`deletedPair Sⁿ (fiber f y)`. The pair map itself depends only on the chosen
separated-neighborhood data `D`; only the homology-isomorphism theorem takes
the explicit proof that the fiber is finite.

The main theorem `Hatcher.Sphere.finitePuncturePairHom_homology_isIso` states
that this morphism induces an isomorphism on relative integral homology in
every degree. Prove the component equation saying that
`sigmaPairι` followed by this map is the direct inclusion of the corresponding
punctured neighborhood pair into the finite-puncture sphere pair, and name
that exact triangle. The target must be the literal deleted-fiber pair, not an
abstract isomorphic object. No positivity, `Fintype`, or nonemptiness premise
is required; the empty fiber is included.

## Depends on

- [Deleted-pair homology is local on an open neighborhood](deleted-pair-open-neighborhood.md)
- [Disjoint punctured neighborhoods form the deleted union pair](disjoint-punctured-pair-iso.md)
- [A finite sphere-map fiber has disjoint isolated neighborhoods](finite-fiber-neighborhoods.md)

## Sources

- [Hatcher §2.2, excision in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
