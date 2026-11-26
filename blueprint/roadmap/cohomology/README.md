# Cohomology

Hatcher's Chapter 3 (pages 185–336). Mapped, not yet decomposed.

Cohomology dualizes homology, and the dualization buys something homology does
not have: a ring structure. `Hⁿ(X; R)` is built by applying `Hom(−, R)` to the
singular chain complex, so it carries the same information up to the Ext terms
that the universal coefficient theorem accounts for. The cup product then makes
`H∗(X; R)` a graded ring, and that ring distinguishes spaces with identical
homology groups.

[Cohomology groups](cohomology-groups/README.md) proves the universal
coefficient theorem and transfers the Chapter 2 machinery to cohomology.

[Cup product](cup-product/README.md) constructs the ring structure, proves a
Künneth formula, and computes the cohomology rings of projective spaces.

[Poincaré duality](poincare-duality/README.md) is the chapter's summit: for a
closed `R`-orientable `n`-manifold, cap product with the fundamental class is
an isomorphism `Hᵏ(M; R) ≅ H_{n−k}(M; R)`.

None of this is in Mathlib, and all of it rests on Chapter 2's excision.
Mathlib has the homological algebra — `Ext`, `Tor`, derived functors — so the
universal coefficient theorem is the most reachable piece once cochains exist.

## Sections

- [Cohomology groups](cohomology-groups/README.md)
- [Cup product](cup-product/README.md)
- [Poincaré duality](poincare-duality/README.md)

## Sources

- [Hatcher, Chapter 3](../../sources/hatcher.md)
