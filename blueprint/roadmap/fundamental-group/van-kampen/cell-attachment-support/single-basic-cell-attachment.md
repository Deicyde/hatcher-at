---
article_id: af_774c47bdf915006fbe45b28e
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.ConeAttachment.attachCells_basicCell
---

# A single cone attachment is a standard cell attachment

For a continuous attaching map from `TopCat.diskBoundary n` into `X`, the
canonical inclusion of `X` into the cone quotient carries a one-cell
`HomotopicalAlgebra.AttachCells` structure for Mathlib's exact
`TopCat.RelativeCWComplex.basicCell n` family.

Formalized as `Hatcher.VanKampen.ConeAttachment.attachCells_basicCell`. The
proof first identifies the retained cone with `TopCat.disk n`, including its
boundary map, then transports the explicit cone pushout along that arrow
isomorphism using Mathlib's `AttachCells.reindexCellTypes`.

This closes the representation bridge for one disk. The remaining roadmap
work is to assemble arbitrary indexed families and Hatcher's connected
auxiliary cover.

## Depends on

- [The cone on a disk boundary is the disk](cone-disk-homeomorphism.md)
- [A single cone attachment is a topological pushout](single-cone-pushout.md)

## Sources

- [Hatcher §1.2, disk attachments in Proposition 1.26](../../../../sources/hatcher-1-2.md)
- [Mathlib's standard cell family](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Topology/CWComplex/Abstract/Basic.lean)
