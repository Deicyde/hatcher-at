---
declaration: corollary
origin: cited
---

# Every group is a fundamental group

**Hatcher, Corollary 1.28 (page 52).** For every group `G`, there is a
two-dimensional cell complex `X_G` with `π₁(X_G) ≃* G`.

Intended artifact: `Hatcher.exists_twoDimensionalCWComplex_fundamentalGroupEquiv`.

Use the generator type of a presentation of `G` to form a wedge of circles,
then attach one 2-cell for each relator. The statement is for arbitrary groups,
not only finitely presented groups.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [Every group admits a generators-and-relations presentation](every-group-presentation.md)
- [The fundamental group of a wedge](wedge-fundamental-group.md)
- [Attaching 2-cells adds the attaching relations](attach-two-cells-fundamental-group.md)
- [The fundamental group of the circle](../basic-constructions/fundamental-group-circle.md)

## Sources

- [Hatcher §1.2, Corollary 1.28](../../../sources/hatcher-1-2.md)
