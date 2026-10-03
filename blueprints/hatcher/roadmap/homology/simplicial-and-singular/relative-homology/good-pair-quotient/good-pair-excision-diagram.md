---
article_id: af_9ac7fe6f41815e0f139260e2
source_units: [hatcher-2-1-good-pair-quotient]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Relative.GoodPairData.pointQuotientExcisionDiagram
---

# The complementary excision diagram

For chosen good-pair data, package Hatcher's page-124 comparison diagram from
the pairs `(X,A)`, `(X,V)`, and `(X ∖ A,V ∖ A)` to their point-quotient
counterparts.

Define the pair map induced by the complement homeomorphism and prove both
canonical squares commute, including the neighborhood comparison identity
used in the final diagram chase. The intended main artifact is
`Hatcher.Relative.GoodPairData.pointQuotientExcisionDiagram`.

Formalized in `Hatcher/Singular/GoodPairExcisionDiagram.lean`. The source and
target complement pairs are packaged explicitly, and
`pointQuotientComplementPairIso` is induced by the canonical homeomorphism
off the collapsed subspace together with its restriction to the deleted
neighborhoods. The theorem `neighborhood_pointQuotientComparison` proves the
left square

`neighborhoodPairHom ≫ neighborhoodPairToPointQuotientNeighborhoodPair =`
`pointQuotientComparison.app P ≫ pointQuotientPairToNeighborhoodPair`,

while `pointQuotientComplement_excisionSquare` proves the right square with
the two canonical `deletedSubsetPairHom` maps. The main artifact packages
these two identities and the exact complement-pair isomorphism; no homology
isomorphism or diagram chase is asserted in this node.

## Depends on

- [Topology of the point-quotient projection](point-quotient-projection-topology.md)
- [Restricting the quotient to a good-pair neighborhood](good-pair-neighborhood-quotient.md)
- [Enlarging to the chosen neighborhood preserves relative homology](good-pair-neighborhood-relative-homology.md)
- [Deleted-subset excision induces homology isomorphisms](../small-chains-and-excision/deleted-subset-excision-homology-isomorphism.md)

## Sources

- [Hatcher §2.1, Proposition 2.22 comparison diagram, page 124](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
