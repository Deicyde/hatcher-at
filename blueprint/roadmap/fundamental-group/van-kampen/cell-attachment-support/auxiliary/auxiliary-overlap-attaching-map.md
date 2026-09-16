---
article_id: af_7e63b8ef03a5c3457a6322f0
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
---

# Overlap meridians recover the attaching loops

For a family of attached `2`-cells, compare the meridian supplied by each
auxiliary overlap piece with the original attaching loop. After applying the
base-side retraction and changing basepoint along the canonical spine path,
the induced element of `FundamentalGroup X x₀` is the attaching map applied to
the standard generator of `TopCat.diskBoundary 2` and conjugated along the
chosen path `γ j`.

Intended artifact:
`Hatcher.VanKampen.AuxiliaryCellAttachment.intersectionMeridian_eq_attachingLoop`.
State the equality with all basepoint transports visible. The result must be
strong enough to identify the normal closure of the overlap image with the
normal closure of Hatcher's transported attaching loops.

## Depends on

- [Every abstract cell attachment has an indexed cone model](../abstract-cell-attachment-indexed-model.md)
- [The auxiliary cover basepoint transports to the original basepoint](auxiliary-cover-basepoint-transport.md)
- [Each overlap piece has the homotopy type of its attaching sphere](auxiliary-overlap-piece-sphere.md)
- [The boundary of the two-disk is the circle](../disk-boundary-two-circle.md)

## Proof depends on

- [The fundamental group of the circle](../../../basic-constructions/fundamental-group-circle.md)

## Sources

- [Hatcher §1.2, loops `δα` and `γα φα γ̄α` on page 50](../../../../../sources/hatcher-1-2.md)
