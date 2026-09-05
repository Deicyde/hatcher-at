---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.ConeAttachment.isPushout_coneAttachment
---

# A single cone attachment is a topological pushout

For a continuous map `f : S → X`, the explicit single-cone attachment is the
pushout in `TopCat` of `f` and the retained-boundary inclusion
`S → ConeAttachment id`.

Formalized as
`Hatcher.VanKampen.ConeAttachment.isPushout_coneAttachment`. The proof builds
the universal map out of the quotient and proves uniqueness on the base, apex,
and cylinder representatives.

The same module packages this square as
`Hatcher.VanKampen.ConeAttachment.attachCells_coneAttachment`, a one-cell
`HomotopicalAlgebra.AttachCells` structure for the retained-cone cell type.
The separate cone-to-disk homeomorphism identifies that cell geometrically
with Mathlib's standard disk; transporting this structure to
`TopCat.RelativeCWComplex.basicCell` is the next bridge.

## Depends on

- [A single cone attachment has a two-set open cover](single-cone-open-cover.md)

## Sources

- [Hatcher §1.2, disk attachments in Proposition 1.26](../../../../sources/hatcher-1-2.md)
- [Mathlib's `AttachCells` pushout interface](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/AlgebraicTopology/RelativeCellComplex/AttachCells.lean)
