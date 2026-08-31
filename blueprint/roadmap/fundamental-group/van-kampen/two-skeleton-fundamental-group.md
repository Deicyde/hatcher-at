---
declaration: proposition
origin: cited
---

# The 2-skeleton determines the fundamental group

**Hatcher, Proposition 1.26(c) (pages 50–51).** For a path-connected CW
complex `X`, inclusion of the 2-skeleton induces an isomorphism
`π₁(X², x₀) ≃* π₁(X, x₀)`.

Intended artifact: `Hatcher.fundamentalGroupEquiv_twoSkeleton`.

Finite-dimensional complexes follow by repeatedly attaching higher cells. In
the general case, compactness places every loop and loop homotopy inside a
finite subcomplex.

State this using Mathlib's classical `Topology.CWComplex` and
`CWComplex.skeleton`. The attachment theorem uses the abstract categorical CW
API, so its use here goes through the explicit bridge node rather than an
unstated identification of the two models.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [Attaching higher cells preserves the fundamental group](attach-higher-cells-fundamental-group.md)
- [Classical skeleton inclusions are abstract cell attachments](../../appendix/classical-skeleton-cell-attachment.md)
- [Compact subsets lie in finite subcomplexes](../../appendix/compact-subspace-finite-subcomplex.md)

## Sources

- [Hatcher §1.2, Proposition 1.26(c)](../../../sources/hatcher-1-2.md)
