---
article_id: af_bb3f77cd307019c6adcf877c
source_units: [hatcher-2-1-good-pair-quotient]
declaration: theorem
origin: bridged
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

## Depends on

- [Good pairs and neighborhood deformation retracts](good-pair-data.md)
- [Topology of the point-quotient projection](point-quotient-projection-topology.md)

## Sources

- [Hatcher §2.1, proof of Proposition 2.22, page 124](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
