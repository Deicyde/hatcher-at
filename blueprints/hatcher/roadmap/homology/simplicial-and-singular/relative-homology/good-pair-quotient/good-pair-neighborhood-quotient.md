---
article_id: af_bb3f77cd307019c6adcf877c
source_units: [hatcher-2-1-good-pair-quotient]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Relative.GoodPairData.pointQuotientNeighborhoodProjection_isQuotientMap
---

# Restricting the quotient to a good-pair neighborhood

For `h : Hatcher.Relative.GoodPairData P`, let `qV` be the image of its chosen
neighborhood under the point-quotient projection. Prove saturation
`q ⁻¹' qV = h.V`, that the restricted map `h.V → qV` is a quotient map, and
that the collapsed point lies in `interior qV`.

The proof must use `Set.range P.map ⊆ interior h.V`; it may not assume
`IsOpen h.V`. Define the canonical neighborhood pairs and the maps needed by
the Proposition 2.22 diagram, together with the two deleted-subset-excision
closure hypotheses.

The set
`pointQuotientNeighborhood` is the image of `h.V`, and
`pointQuotientProjection_preimage_neighborhood` proves its inverse image is
exactly `h.V`. The restricted continuous map
`pointQuotientNeighborhoodProjection` is surjective and a quotient map. Its
proof works with ambient open representatives of open subsets of `h.V`: each
representative either contains the entire collapsed range or avoids it, hence
is saturated for the global quotient projection. No openness assumption is
placed on `h.V`.

The theorem `pointQuotientPoint_mem_interior_neighborhood` obtains an open
neighborhood of the collapsed point by projecting `interior h.V`. The module
also supplies the two exact closure-in-interior hypotheses for deleted-subset
excision, packages `(X/A,V/A)` as `pointQuotientNeighborhoodPair`, and defines
the canonical maps from `(X/A,A/A)` and `(X,V)` into that pair.

## Depends on

- [Good pairs and neighborhood deformation retracts](good-pair-data.md)
- [Topology of the point-quotient projection](point-quotient-projection-topology.md)

## Sources

- [Hatcher §2.1, proof of Proposition 2.22, page 124](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
