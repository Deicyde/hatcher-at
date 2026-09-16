---
article_id: af_7f02274bbda3e997009bd431
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
---

# Each overlap piece has the homotopy type of its attaching sphere

For every attached `n`-cell, construct a based homotopy equivalence from the
corresponding member of the auxiliary overlap cover to
`TopCat.diskBoundary n`. Its whisker runs from the common overlap basepoint
through the shared spine and strip to the selected boundary point; after that
whisker is collapsed, the remaining punctured cell retracts radially onto its
boundary sphere.

Intended artifact:
`Hatcher.VanKampen.AuxiliaryCellAttachment.intersectionPieceHomotopyEquivBoundary`.
This equivalence supplies the higher-dimensional triviality argument. Its
compatibility with the original attaching maps is a separate two-dimensional
node.

## Depends on

- [The auxiliary overlap has an indexed open cover](auxiliary-overlap-open-cover.md)

## Proof depends on

- [The single-cone cover intersection has the homotopy type of its boundary](../single-cone-intersection.md)

## Sources

- [Hatcher §1.2, deformation of each `Aα` on pages 50–51](../../../../../sources/hatcher-1-2.md)
