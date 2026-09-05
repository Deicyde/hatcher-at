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
`TopCat.disk n`. The single-cone quotient is also proved to be a `TopCat`
pushout and carries a one-cell `HomotopicalAlgebra.AttachCells` structure for
its retained-cone boundary. Its base-side cover strongly deformation-retracts
onto `X`, and its cone-side cover is contractible. An indexed quotient with one
apex per cell and the correct empty-family behavior is also formalized, but its
upper cover is generally disconnected. The remaining geometry is Hatcher's
connected auxiliary cover and the open cover of its intersection. For a single
disk, the explicit quotient is now connected to Mathlib's exact
`TopCat.RelativeCWComplex.basicCell`; extending this comparison to the indexed
construction remains. The final statement also needs an explicit basepoint and
a dimension hypothesis. Those interfaces must be fixed without hiding the
geometric content.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [A single cone attachment has a two-set open cover](cell-attachment-support/single-cone-open-cover.md)
- [An indexed family of cones has a two-set open cover](cell-attachment-support/indexed-cone-open-cover.md)
- [The base-side cone cover retracts onto the original space](cell-attachment-support/single-cone-base-retract.md)
- [The cone-side cover member is contractible](cell-attachment-support/single-cone-upper-contractible.md)
- [The cone on a disk boundary is the disk](cell-attachment-support/cone-disk-homeomorphism.md)
- [A single cone attachment is a topological pushout](cell-attachment-support/single-cone-pushout.md)
- [A single cone attachment is a standard cell attachment](cell-attachment-support/single-basic-cell-attachment.md)

## Sources

- [Hatcher §1.2, construction used in Proposition 1.26 on pages 49–51](../../../sources/hatcher-1-2.md)
