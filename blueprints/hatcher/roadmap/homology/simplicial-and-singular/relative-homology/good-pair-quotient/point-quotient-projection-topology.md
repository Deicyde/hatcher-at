---
article_id: af_dda9959596a494d3473c0349
source_units: [hatcher-2-1-good-pair-quotient]
declaration: def
origin: background
statement: formalized
proof: formalized
lean: Hatcher.Relative.pointQuotientComplementHomeomorph
---

# Topology of the point-quotient projection

For a topological pair with nonempty subspace, prove that the ambient point-
quotient projection is a quotient map and that the inverse image of the
collapsed point is exactly `Set.range P.map`. When that range is closed, deduce
that the collapsed point is closed.

Construct the canonical homeomorphism

`P.fst ∖ Set.range P.map ≃ₜ (X/A) ∖ {collapsedPoint}`.

The intended completion target is
`Hatcher.Relative.pointQuotientComplementHomeomorph`, with the quotient-map
and fibre theorems as supporting results in the same review unit.

Formalized in `Hatcher/Singular/PointQuotientTopology.lean`. For nonempty
`P.snd`, `pointQuotientProjection_isQuotientMap` proves that the ambient
projection is a quotient map, and `pointQuotientProjection_preimage_point`
identifies its collapsed fibre with `Set.range P.map`.
`pointQuotientPoint_isClosed` transfers closedness of this range to the
collapsed point. Under the same closedness hypothesis,
`pointQuotientComplementHomeomorph` restricts the canonical projection to the
displayed homeomorphism; its simp lemma records that the forward map is
literally the quotient projection.

## Depends on

- [Functorial point quotients of topological pairs](point-quotient-functor.md)

## Sources

- [Hatcher §2.1, quotient map off the subspace, page 124](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
