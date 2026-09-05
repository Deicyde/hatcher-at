---
declaration: proposition
origin: cited
---

# Attaching 2-cells adds the attaching relations

**Hatcher, Proposition 1.26(a) (page 50).** If `Y` is obtained from a
path-connected space `X` by attaching an arbitrary family of 2-cells, then
`π₁(X) → π₁(Y)` is surjective and its kernel is the normal closure of the
attaching loops, transported to the common basepoint. Hence `π₁(Y)` is the
corresponding quotient of `π₁(X)`.

Intended artifact: `Hatcher.fundamentalGroup_quotient_of_attachTwoCells`.

The statement must expose the chosen basepoint paths but prove that the normal
subgroup is independent of those choices, as Hatcher notes after the
proposition.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [An open-cover model for attached cells](cell-attachment-cover-model.md)
- [The attaching-sphere pieces generate the intersection group](attaching-spheres-generate-intersection.md)
- [A binary cover with a trivial second fundamental group](binary-cover-trivial-piece-quotient.md)
- [Retractions and deformation retracts on the fundamental group](../basic-constructions/retractions-fundamental-group.md)
- [The fundamental group of the circle](../basic-constructions/fundamental-group-circle.md)

## Sources

- [Hatcher §1.2, Proposition 1.26(a)](../../../sources/hatcher-1-2.md)
