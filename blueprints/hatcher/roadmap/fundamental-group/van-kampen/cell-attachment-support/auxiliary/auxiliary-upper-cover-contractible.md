---
article_id: af_4d712408a8cbf7efd1b49e64
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.AuxiliaryCellAttachment.contractibleSpace_upperCover
---

# The strip-connected upper cover is contractible

For a nonempty family of cells, prove that the upper member of Hatcher's
auxiliary cover is contractible. Contract each truncated cone neighborhood
through its attached strip to the common spine, then contract that spine to the
chosen overlap basepoint. The construction must remain continuous for an
arbitrary index type and must not identify the distinct cone apices in the
ambient attachment.

Intended artifact:
`Hatcher.VanKampen.AuxiliaryCellAttachment.contractibleSpace_upperCover`.

## Depends on

- [Hatcher's binary cover of the strip enlargement](auxiliary-cell-attachment-open-cover.md)

## Proof depends on

- [The cone-side cover member is contractible](../single-cone-upper-contractible.md)

## Sources

- [Hatcher §1.2, proof of Proposition 1.26 on page 50](../../../../../sources/hatcher-1-2.md)
