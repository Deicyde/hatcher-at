---
article_id: af_d40cc60ada4364ba06f00457
source_units: [hatcher-1-2-selected-spine]
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.exists_cellAttachmentCover
---

# An open-cover model for attached cells

Let `c : HomotopicalAlgebra.AttachCells.{u}
(TopCat.RelativeCWComplex.basicCell n) f`, where `X` is path-connected, the
cell-index type is nonempty, and `1 < n`. For a basepoint `x₀ : X`, a chosen
point `s₀ : TopCat.diskBoundary n`, and paths from `x₀` to every attaching
point, construct Hatcher's auxiliary cover package for `c`.

Intended artifact: `Hatcher.VanKampen.exists_cellAttachmentCover`.

The result returns `Nonempty (CellAttachmentCover c x₀ s₀ γ)`. This package
contains the strip-enlarged space `Z`, its strong deformation retraction onto
the indexed model of the target, the open cover `A ∪ B`, the strong deformation
retraction `A → X`, a contraction of `B`, and the pointed indexed cover of
`A ∩ B` by pieces homotopy equivalent to the disk boundary. It also records the
spine path from the overlap basepoint to the image of `x₀` and the exact
basepoint-change equations induced by the lower retraction.

State the input using `HomotopicalAlgebra.AttachCells` for
`TopCat.RelativeCWComplex.basicCell n`. This node is the final integrator of the
geometric work shared by Proposition 1.26(a) and (b); it does not calculate
`π₁(A ∩ B)` or assert either final fundamental-group result. The empty-index
case is intentionally handled by a separate isomorphism rather than by adding
a dummy cell to the connected cover.

## Depends on

- [Every abstract cell attachment has an indexed cone model](cell-attachment-support/abstract-cell-attachment-indexed-model.md)
- [The strip-enlarged cell-attachment space](cell-attachment-support/auxiliary/auxiliary-cell-attachment-space.md)

## Proof depends on

- [The strip enlargement retracts onto the attached space](cell-attachment-support/auxiliary/auxiliary-attachment-retract.md)
- [Hatcher's binary cover of the strip enlargement](cell-attachment-support/auxiliary/auxiliary-cell-attachment-open-cover.md)
- [The base-side auxiliary cover retracts onto the original space](cell-attachment-support/auxiliary/auxiliary-base-cover-retract.md)
- [The strip-connected upper cover is contractible](cell-attachment-support/auxiliary/auxiliary-upper-cover-contractible.md)
- [The auxiliary cover basepoint transports to the original basepoint](cell-attachment-support/auxiliary/auxiliary-cover-basepoint-transport.md)
- [The auxiliary overlap has an indexed open cover](cell-attachment-support/auxiliary/auxiliary-overlap-open-cover.md)
- [Each overlap piece has the homotopy type of its attaching sphere](cell-attachment-support/auxiliary/auxiliary-overlap-piece-sphere.md)

## Sources

- [Hatcher §1.2, construction used in Proposition 1.26 on pages 49–51](../../../sources/hatcher-1-2.md)
