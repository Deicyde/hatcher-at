---
article_id: af_3482f234b914950daa685013
source_units: [hatcher-2-2-local-degree]
declaration: def
origin: bridged
---

# Disjoint punctured neighborhoods form the deleted union pair

Let `U i` be pairwise disjoint open subsets of `X` and choose `x i ∈ U i`.
The sigma pair of the punctured neighborhood pairs has ambient space
`Σ i, U i` and deletes one point in each summand. Construct the canonical pair
isomorphism from this sigma pair to the union `⋃ i, U i` with the range of the
points `x i` deleted.

The main artifact is
`Hatcher.Relative.sigmaPuncturedPairIsoDeletedUnion`. Its ambient component is
`sigmaSubtypeHomeomorphUnion`, and its component formula identifies each
`sigmaPairι` with the ordinary inclusion of `(U i,U i-{x i})` into the deleted
union pair.

Represent the target subspace as the preimage
`Subtype.val ⁻¹' (Set.range x)ᶜ` inside `⋃ i, U i`, so it aligns with the later
`deletedPairWithin` API. Name both the sigma punctured source pair and deleted
union target pair. Construct the subspace homeomorphism without assuming that
the punctured sets are open; no `T1Space X` hypothesis belongs here.

Expose the direct local inclusion
`Hatcher.Relative.puncturedNeighborhoodDeletedUnionPairHom`, ambient and
proof-term-insensitive subspace component formulas, and the exact triangle

`sigmaPairι i ≫ sigmaPuncturedPairIsoDeletedUnion.hom =`
`  puncturedNeighborhoodDeletedUnionPairHom i`.

The definitions require no `Nonempty ι` hypothesis and include the empty
family.

## Depends on

- [The coproduct of a family of topological pairs](sigma-topological-pair.md)
- [A disjoint open family is homeomorphic to its sigma type](disjoint-open-union-homeomorphism.md)
- [Local homology is unchanged on an open neighborhood](../local-homology-and-dimension/local-homology-open-neighborhood.md)

## Sources

- [Hatcher §2.2, disjoint local pairs in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
