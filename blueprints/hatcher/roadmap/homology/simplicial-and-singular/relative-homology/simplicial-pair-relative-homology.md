---
article_id: af_2a09c48fe99a73a2e9df0d1a
source_units: [hatcher-2-1-relative-homology-les]
declaration: def
origin: bridged
not_ready: true
---

# Relative homology of a simplicial-set pair

For a monomorphism `A ⟶ X` of simplicial sets, form the cokernel chain
complex `Cₙ(X;R) / Cₙ(A;R)`, its homology functor, the quotient map from
absolute chains, and the connecting morphisms and exactness results relating
the homology of `A`, `X`, and `(X,A)`.

After a Mathlib pin update, the main artifact is the upstream definition
`SSetPair.homologyFunctor` in
`Mathlib/AlgebraicTopology/SimplicialSet/Homology/Relative.lean`; its supporting
API includes `SSetPair.chainComplex`, `homologyπ`, `homologyδ`, and
`homology_exact₁/₂/₃`.

This node is not ready at the current `v4.31.0` pin. It may be marked as exact
Mathlib coverage only after Setup moves the project to a stable release
containing PR #41285 and Autoform verifies the declaration and module.

## Depends on

- [A chain map induces a map on homology](../chain-map-homology.md)

## Sources

- [Hatcher §2.1, relative chains, pages 115–116](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
