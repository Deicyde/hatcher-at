---
article_id: af_51e96e7c13ef33c86536df2b
source_units: [hatcher-2-1-selected-spine]
declaration: lemma
origin: cited
mathlib: true
mathlib_declaration: TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
mathlib_file: Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean
---

# Homotopic maps induce the same singular-homology map

**Hatcher, Theorem 2.10 (pages 111–113).** If continuous maps `f,g : X → Y`
are homotopic, their induced maps on singular homology are equal in every
degree. The exact pinned statement is
`homologyMap (((singularChainComplexFunctor C).obj R).map f) n =
homologyMap (((singularChainComplexFunctor C).obj R).map g) n`.

This is exactly the pinned lemma
`TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`.

## Depends on

- [The singular chain complex](singular-chain-complex.md)
- [A chain map induces a map on homology](chain-map-homology.md)

## Proof depends on

- [Chain-homotopic maps induce the same homology map](chain-homotopy-invariance.md)
- [A topological homotopy gives a singular-chain homotopy](topological-homotopy-chain-homotopy.md)

## Sources

- [Hatcher §2.1, Theorem 2.10](../../../sources/hatcher-2-1.md)
