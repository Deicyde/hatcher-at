---
article_id: af_64e2faf664f742dcc73fca0a
source_units: [hatcher-2-1-post-excision-applications]
declaration: theorem
origin: cited
---

# Local homology is unchanged on an open neighborhood

For a space `X` and `x : X`, define the punctured topological pair
`Hatcher.Relative.puncturedPair X x := (X, X \ {x})`. If `U : Set X` is an
open neighborhood of `x`, and `{x}` is closed in `X`, define the canonical
pair morphism from the punctured pair in `U` to the punctured pair in `X`.

The main result
`Hatcher.Relative.localHomologyOpenNeighborhoodMap_isIso` states that this
canonical map induces an isomorphism on relative homology in every degree and
for every supported coefficient object under the explicit hypothesis
`IsClosed ({x} : Set X)` (or a `T1Space X` specialization). Also package the
pair isomorphism and induced homology isomorphism associated to a homeomorphism
carrying `x` to `y`.

This is Hatcher's local-homology observation following Theorem 2.26. Prove the
open-neighborhood comparison with the completed excision API; do not replace
the named inclusion-induced map by an arbitrary isomorphism.

## Depends on

- [Relative singular chains and homology](../../simplicial-and-singular/relative-homology/relative-singular-homology.md)

## Proof depends on

- [Deleted-subset homology excision](../../simplicial-and-singular/relative-homology/small-chains-and-excision/deleted-subset-excision-homology-isomorphism.md)

## Sources

- [Hatcher §2.1, local homology after Theorem 2.26, page 126](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
