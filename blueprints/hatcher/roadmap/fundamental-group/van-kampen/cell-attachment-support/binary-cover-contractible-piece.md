---
article_id: af_8c128342fc57668c60bffac3
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.fundamentalGroupEquivOfBinaryCoverRetraction
---

# A binary cover with a contractible second piece

Let two path-connected open sets cover `Y`. Suppose the second member is
contractible, their intersection is simply connected, and the first member
strongly deformation retracts onto the image of a space `A`. Then inclusion
induces an equivalence `π₁(A) ≃* π₁(Y)`.

Formalized as
`Hatcher.VanKampen.fundamentalGroupEquivOfBinaryCoverRetraction` in
`Hatcher/VanKampen/CellAttachmentAlgebra.lean`. The same module proves the
underlying algebraic fact that a binary group pushout with trivial
amalgamating group and trivial second factor is equivalent to its first
factor, and records that the resulting equivalence is induced by inclusion.

This is the algebraic endgame of the higher-cell attachment argument. The
point-set construction of Hatcher's auxiliary cover and the proof that its
intersection is simply connected remain separate geometric prerequisites.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [Binary van Kampen is a group pushout](../binary-van-kampen-pushout.md)
- [Retractions and deformation retracts on the fundamental group](../../basic-constructions/retractions-fundamental-group.md)

## Sources

- [Hatcher §1.2, proof of Proposition 1.26(b), pages 50–51](../../../../sources/hatcher-1-2.md)
