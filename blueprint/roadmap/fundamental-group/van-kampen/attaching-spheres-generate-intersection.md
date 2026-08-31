---
declaration: theorem
origin: bridged
---

# The attaching-sphere pieces generate the intersection group

For Hatcher's auxiliary cover of an `n`-cell attachment, the path-connected
space `A ∩ B` is covered by open pieces indexed by the attached cells. Each
piece deformation retracts onto the corresponding attaching
`(n-1)`-sphere, and the maps from their fundamental groups jointly generate
`π₁(A ∩ B)`.

Intended artifact:
`Hatcher.VanKampen.attachmentIntersection_coverMap_surjective`.

The two attachment nodes specialize this surjectivity statement. For `n = 2`,
they identify generators using the circle computation. For `n > 2`, they use
Proposition 1.14 to show that every source group, and hence the intersection
group, is trivial.

## Depends on

- [An open-cover model for attached cells](cell-attachment-cover-model.md)

## Proof depends on

- [The van Kampen cover map is surjective](van-kampen-surjective.md)

## Sources

- [Hatcher §1.2, proof of Proposition 1.26 on pages 50–51](../../../sources/hatcher-1-2.md)
