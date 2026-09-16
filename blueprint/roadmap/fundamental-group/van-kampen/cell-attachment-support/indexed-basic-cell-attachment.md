---
article_id: af_a19e022e940644366ba5f04a
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.IndexedConeAttachment.attachCells_basicCell
---

# An indexed cone attachment is a standard cell attachment

Fix a dimension `n`. For a family of continuous maps from
`TopCat.diskBoundary n` to `X`, equip the canonical base inclusion into the
indexed cone quotient with a `HomotopicalAlgebra.AttachCells` structure for
Mathlib's exact family `TopCat.RelativeCWComplex.basicCell n`.

Intended artifact:
`Hatcher.VanKampen.IndexedConeAttachment.attachCells_basicCell`.
It should first package the indexed pushout with one retained cone per index,
then transport every cell arrow through the already formalized cone-to-disk
homeomorphism. The initial interface uses `AttachCells.{u}` with the cell index
in `Type u`; support for a separately sized index type is a later resizing
problem, not an implicit assumption here.

## Depends on

- [An indexed family of cone attachments is a topological pushout](indexed-cone-pushout.md)
- [The cone on a disk boundary is the disk](cone-disk-homeomorphism.md)

## Sources

- [Hatcher §1.2, disk attachments in Proposition 1.26](../../../../sources/hatcher-1-2.md)
- [Mathlib's standard cell family](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Topology/CWComplex/Abstract/Basic.lean)
