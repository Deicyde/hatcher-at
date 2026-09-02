---
declaration: def
origin: cited
mathlib: true
mathlib_declaration: AlgebraicTopology.singularChainComplexFunctor
mathlib_file: Mathlib/AlgebraicTopology/SingularHomology/Basic.lean
---

# The singular chain complex

For a coefficient object `R` in a preadditive category with coproducts and a
topological space `X`, form the chain complex freely generated in degree `n`
by continuous maps from the standard `n`-simplex to `X`, with differential the
alternating sum of face restrictions.

The pinned definition
`AlgebraicTopology.singularChainComplexFunctor` packages this construction as
a functor in both the coefficient object and the space. Its implementation is
the chain complex of the singular simplicial set `TopCat.toSSet.obj X`.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §2.1, singular chains, pages 108–109](../../../sources/hatcher-2-1.md)
