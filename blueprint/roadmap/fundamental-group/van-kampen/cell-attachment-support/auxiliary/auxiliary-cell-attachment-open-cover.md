---
article_id: af_1a04a09d1dd81895c2a78411
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
---

# Hatcher's binary cover of the strip enlargement

Assume the cell-index type is nonempty. In the strip-enlarged attachment,
define the base-side member by omitting every cone apex and the upper member by
omitting the canonical copy of `X`, using saturated height inequalities in the
quotient model. Prove that the two sets are open and cover `Z`, and construct a
common basepoint on the shared spine together with the path-connectedness data
needed by binary van Kampen.

Intended artifact:
`Hatcher.VanKampen.AuxiliaryCellAttachment.isOpenCover_base_upper`.
The same module should expose `baseCover`, `upperCover`, their inclusions, and
the chosen overlap basepoint. It does not yet prove either deformation
retraction or calculate the overlap fundamental group.

## Depends on

- [The strip-enlarged cell-attachment space](auxiliary-cell-attachment-space.md)

## Sources

- [Hatcher §1.2, cover `A ∪ B` on page 50](../../../../../sources/hatcher-1-2.md)
