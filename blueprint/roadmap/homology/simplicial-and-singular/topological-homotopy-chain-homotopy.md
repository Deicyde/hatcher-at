---
declaration: def
origin: bridged
mathlib: true
mathlib_declaration: TopCat.Homotopy.singularChainComplexFunctorObjMap
mathlib_file: Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean
---

# A topological homotopy gives a singular-chain homotopy

For homotopic maps `f,g : X ⟶ Y`, the induced maps between singular chain
complexes are chain homotopic.

The pinned definition
`TopCat.Homotopy.singularChainComplexFunctorObjMap` constructs this homotopy
through the singular simplicial set. It fills the same role as Hatcher's prism
operator, but it is not a formalization of Hatcher's explicit prism formula.

## Depends on

- [The singular chain complex](singular-chain-complex.md)

## Sources

- [Hatcher §2.1, proof of Theorem 2.10](../../../sources/hatcher-2-1.md)
