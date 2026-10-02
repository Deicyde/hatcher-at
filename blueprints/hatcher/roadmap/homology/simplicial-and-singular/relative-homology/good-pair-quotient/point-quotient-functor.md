---
article_id: af_87cd8f5d6a5cc82bf5766bcf
source_units: [hatcher-2-1-good-pair-quotient]
declaration: def
origin: background
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

## Depends on

None.

## Sources

- [Hatcher §2.1, quotient pair in Proposition 2.22, page 124](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
