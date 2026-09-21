---
article_id: af_43621dbc2063991527df5593
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: cited
---

# The 2-skeleton determines the fundamental group

**Hatcher, Proposition 1.26(c) (pages 50–51).** For a path-connected CW
complex `X`, inclusion of the 2-skeleton induces an isomorphism
`π₁(X², x₀) ≃* π₁(X, x₀)`.

Intended artifact: `Hatcher.fundamentalGroupEquiv_twoSkeleton`.

State this using Mathlib's classical `Topology.CWComplex` and
`CWComplex.skeleton`. The induced homomorphism is an isomorphism because it is
both surjective and injective. For surjectivity, put the compact image of a
representative loop inside a bounded skeleton and use the finite-stage
equivalence. For injectivity, do the same with the compact image of a null
homotopy and use the finite-stage equivalence's application lemma. This is the
two-use compactness argument in Hatcher's proof.

Do not silently assume that the 2-skeleton is path-connected. That instance is
an explicit prerequisite, and each finite-stage comparison transports the
basepoint along the actual subtype inclusion.

## Depends on

- [Finite skeleta above dimension two have the same fundamental group](finite-skeleton-fundamental-group.md)
- [Compact subsets lie in a bounded skeleton](../../appendix/classical-cw-bridge/compact-subset-bounded-skeleton.md)

## Sources

- [Hatcher §1.2, Proposition 1.26(c)](../../../sources/hatcher-1-2.md)
