---
article_id: af_87cd8f5d6a5cc82bf5766bcf
source_units: [hatcher-2-1-good-pair-quotient]
declaration: def
origin: background
statement: formalized
proof: formalized
lean: Hatcher.Relative.pointQuotientPairFunctor
---

# Functorial point quotients of topological pairs

For every `P : TopPair`, define the point quotient of its ambient space as the
TopCat pushout `P.fst ⊔_{P.snd} PUnit`. Package the pushout point as a pointed
topological pair.

The intended main declaration is
`Hatcher.Relative.pointQuotientPairFunctor : TopPair ⥤ TopPair`. Include the
ambient projection, collapsed point, induced quotient map for every morphism
of pairs, and the natural comparison
`Hatcher.Relative.pointQuotientComparison : 𝟭 TopPair ⟶ pointQuotientPairFunctor`.
Identify each target canonically with the existing `pointedPair` construction.

The supporting API exposes `pointQuotientCollapse`, `pointQuotient`,
`pointQuotientProjection`, `pointQuotientPointInclusion`,
`pointQuotientPoint`, `pointQuotientPair`, and `pointQuotientMap`. The target
pair is defined using `pointedPair`, and `pointQuotientPair_map` identifies
its structure map with the pushout point inclusion. The functor acts on every
morphism of topological pairs, without a good-pair hypothesis, and
`pointQuotientComparison` is the natural map from a pair to its pointed
quotient. This node uses only the pushout universal property; quotient-map,
fibre, and complement topology remain in the next node.

## Depends on

None.

## Sources

- [Hatcher §2.1, quotient pair in Proposition 2.22, page 124](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
