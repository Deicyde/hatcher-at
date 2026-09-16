---
article_id: af_01425aa8a8d4928d8039e3e6
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
---

# The auxiliary overlap has an indexed open cover

Cover the overlap of Hatcher's two auxiliary members by sets indexed by the
attached cells. The `j`-th member retains the common spine and strip system and
the punctured `j`-th cell, while omitting the interiors of the other cells.
Prove that these sets are open in the overlap, cover it, contain the chosen
basepoint, and have the path-connected pairwise intersections required for the
surjective clause of van Kampen.

Intended artifact:
`Hatcher.VanKampen.AuxiliaryCellAttachment.isOpenCover_intersectionPieces`.
The statement assumes a nonempty cell-index type and carries the exact
basepoint membership and path-connectedness witnesses consumed by
`Hatcher.VanKampen.coverMap_surjective`.

## Depends on

- [Hatcher's binary cover of the strip enlargement](auxiliary-cell-attachment-open-cover.md)

## Sources

- [Hatcher §1.2, cover of `A ∩ B` by the sets `Aα` on pages 50–51](../../../../../sources/hatcher-1-2.md)
