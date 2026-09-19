---
article_id: af_b4073e48cecc2c23414164fb
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
lean: Hatcher.VanKampen.AuxiliaryCellAttachment.attachmentStrongDeformationRetract
---

# The strip enlargement retracts onto the attached space

For Hatcher's auxiliary space `Z`, construct a strong deformation retraction
onto the canonical copy of the indexed cone attachment. On every added square,
collapse the square onto its bottom and right edges while fixing those edges;
fix the indexed attachment throughout.

Intended artifact:
`Hatcher.VanKampen.AuxiliaryCellAttachment.attachmentStrongDeformationRetract`.
The module must also record that the inclusion of `X` through the indexed
attachment agrees with the direct base map into `Z`.

## Depends on

- [The strip-enlarged cell-attachment space](auxiliary-cell-attachment-space.md)

## Sources

- [Hatcher §1.2, proof of Proposition 1.26 on page 50](../../../../../sources/hatcher-1-2.md)
