---
declaration: lemma
origin: bridged
not_ready: true
---

# An open-cover model for attached cells

For a family of fixed-dimensional cells attached to a path-connected space
`X`, construct Hatcher's auxiliary space `Z`, homotopy equivalent to the
pushout `Y`, with a deformation retraction `Z → Y` and a two-set open cover
`A ∪ B`. The construction must identify `A ≃ X`, prove `B` contractible, and
equip the path-connected intersection `A ∩ B` with Hatcher's open cover whose
pieces deformation retract onto the attaching spheres transported to the
common basepoint.

Intended artifact: `Hatcher.VanKampen.exists_cellAttachmentCover`.

State the input using `HomotopicalAlgebra.AttachCells` for
`TopCat.RelativeCWComplex.basicCell n`. This node packages the geometric work
shared by Proposition 1.26(a) and (b); it does not calculate `π₁(A ∩ B)` or
assert either final fundamental-group result.

This node is not yet ready to formalize against the pinned Mathlib API.
`HomotopicalAlgebra.AttachCells` supplies an abstract coproduct and pushout but
no point-set adjunction-space model, embedding of the original space, disk
collar, mapping-cylinder construction, or deformation-retraction data. The
statement also needs an explicit basepoint, a dimension hypothesis, and an
empty-family case. Those interfaces must be fixed before the open sets and
their intersection cover can be stated without hiding the geometric content.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2, construction used in Proposition 1.26 on pages 49–51](../../../sources/hatcher-1-2.md)
