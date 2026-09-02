---
declaration: def
origin: cited
mathlib: true
mathlib_declaration: AlgebraicTopology.singularHomologyFunctor
mathlib_file: Mathlib/AlgebraicTopology/SingularHomology/Basic.lean
---

# Singular homology

For a coefficient object `R`, a space `X`, and `n : ℕ`, define `Hₙ(X; R)` as
the degree-`n` homology object of the singular chain complex of `X`.

The pinned definition `AlgebraicTopology.singularHomologyFunctor` is functorial
in `R` and `X`. Hatcher's group `Hₙ(X)` is its specialization to abelian groups
with coefficient object `ℤ`.

## Depends on

- [The singular chain complex](singular-chain-complex.md)

## Sources

- [Hatcher §2.1, singular homology, pages 108–109](../../../sources/hatcher-2-1.md)
