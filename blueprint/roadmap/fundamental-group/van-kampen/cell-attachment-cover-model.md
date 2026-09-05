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

This node is not yet ready to formalize against the pinned Mathlib API. The
single-cone quotient and its two open cover members are now explicit, and the
identity attachment on `TopCat.diskBoundary n` has been identified with
`TopCat.disk n`. The arbitrary-family construction still needs one apex per
cell, deformation retractions of both cover members, and the intersection
cover.
`HomotopicalAlgebra.AttachCells` supplies an abstract coproduct and pushout but
no comparison with this point-set adjunction model. The final statement also
needs an explicit basepoint, a dimension hypothesis, and an empty-family case.
Those interfaces must be fixed without hiding the geometric content.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [A single cone attachment has a two-set open cover](cell-attachment-support/single-cone-open-cover.md)
- [The cone on a disk boundary is the disk](cell-attachment-support/cone-disk-homeomorphism.md)

## Sources

- [Hatcher §1.2, construction used in Proposition 1.26 on pages 49–51](../../../sources/hatcher-1-2.md)
