---
declaration: proposition
origin: cited
---

# Attaching higher cells preserves the fundamental group

**Hatcher, Proposition 1.26(b) (pages 50–51).** If `Y` is obtained from a
path-connected space `X` by attaching cells of one fixed dimension `n > 2`,
then inclusion induces an isomorphism `π₁(X, x₀) ≃* π₁(Y, x₀)`.

Intended artifact: `Hatcher.fundamentalGroupEquiv_of_attachCells_of_two_lt`.

The same two-set model as in part (a) applies. The cover pieces of its
intersection now deformation retract onto `(n-1)`-spheres, whose fundamental
groups are trivial.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [An open-cover model for attached cells](cell-attachment-cover-model.md)
- [The attaching-sphere pieces generate the intersection group](attaching-spheres-generate-intersection.md)
- [A binary cover with a contractible second piece](cell-attachment-support/binary-cover-contractible-piece.md)
- [Higher spheres are simply connected](../basic-constructions/sphere-simply-connected.md)

## Sources

- [Hatcher §1.2, Proposition 1.26(b)](../../../sources/hatcher-1-2.md)
