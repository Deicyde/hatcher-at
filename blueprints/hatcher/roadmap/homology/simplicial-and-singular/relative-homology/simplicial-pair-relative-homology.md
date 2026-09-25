---
article_id: af_2a09c48fe99a73a2e9df0d1a
source_units: [hatcher-2-1-relative-homology-les]
declaration: def
origin: bridged
mathlib: true
mathlib_declaration: SSetPair.homologyFunctor
mathlib_file: Mathlib/AlgebraicTopology/SimplicialSet/Homology/Relative.lean
---

# Relative homology of a simplicial-set pair

For a monomorphism `A ⟶ X` of simplicial sets, form the cokernel chain
complex `Cₙ(X;R) / Cₙ(A;R)`, its homology functor, the quotient map from
absolute chains, and the connecting morphisms and exactness results relating
the homology of `A`, `X`, and `(X,A)`.

At the current Mathlib `v4.34.1` pin, the main artifact is the upstream
definition `SSetPair.homologyFunctor` in
`Mathlib/AlgebraicTopology/SimplicialSet/Homology/Relative.lean`; its supporting
API includes `SSetPair.chainComplex`, `homologyπ`, `homologyδ`, and
`homology_exact₁/₂/₃`.

Mathlib `v4.34.1` contains PR #41285, so this foundational node is complete.
[The singular-pair functor](singular-pair-functor.md) is now formalized, and
[relative singular homology](relative-singular-homology.md) is the next ready
node.

## Depends on

- [A chain map induces a map on homology](../chain-map-homology.md)

## Sources

- [Hatcher §2.1, relative chains, pages 115–116](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
