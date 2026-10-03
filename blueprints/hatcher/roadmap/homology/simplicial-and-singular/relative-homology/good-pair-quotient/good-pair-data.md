---
article_id: af_ad99652fe9860290c388915f
source_units: [hatcher-2-1-good-pair-quotient]
declaration: structure
origin: cited
statement: formalized
lean: Hatcher.Relative.GoodPairData
---

# Good pairs and neighborhood deformation retracts

For `P : TopPair`, define `Hatcher.Relative.GoodPairData P` to contain a
nonempty subspace, closedness of `Set.range P.map`, a set `V : Set P.fst`
with `Set.range P.map ⊆ interior V`, and a strong deformation retraction of
`V` onto the embedded subspace.

Define `Hatcher.Relative.IsGoodPair P := Nonempty (GoodPairData P)` and the
full subcategory of good pairs. Morphisms are ordinary morphisms of
topological pairs and do not preserve the chosen witness data. The neighborhood
field is not required to be open: this states Hatcher's hypothesis exactly.

## Depends on

- [Strong deformation retracts](strong-deformation-retract.md)

## Sources

- [Hatcher §2.1, definition of good pairs, page 114](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
