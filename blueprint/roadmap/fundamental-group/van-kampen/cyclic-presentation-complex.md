---
article_id: af_f9c5fec59717acad10d01cee
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: cited
statement: formalized
lean: Hatcher.fundamentalGroupEquiv_cyclicPresentationComplex
---

# The cyclic presentation complex

**Hatcher, Example 1.29 (page 52), group calculation only.** For a positive
natural number `n`, attach a 2-cell to `S¹` along the degree-`n` map. The
resulting presentation complex has fundamental group isomorphic to `ℤ/nℤ`.

Intended artifact: `Hatcher.fundamentalGroupEquiv_cyclicPresentationComplex`.

Define `cyclicPresentationComplex n` as the singleton indexed cone attachment
to `Circle`, using the boundary-of-the-two-disk homeomorphism followed by
`Circle.degreeMap n` as attaching map, and use the image of `1` as basepoint.
`IndexedConeAttachment.attachCells_basicCell` supplies the required abstract
2-cell attachment, so the generic attachment theorem and the cyclic quotient
calculation now complete the group computation.

The Lean artifact is defined for every `n : ℕ`. Its positive cases are exactly
Hatcher's example; at `n = 0` the same construction yields the valid extension
with fundamental group `ZMod 0 ≃+ ℤ`.

The quotient calculation after the geometric step is already formalized in
[The degree-n circle relation gives the cyclic group](cell-attachment-support/cyclic-relation-quotient.md).

This node does not claim the example's later geometric assertions identifying
the `n = 2` case with `ℝP²` or excluding embeddings and surface structures for
higher `n`.

## Depends on

- [An indexed family of cones has a two-set open cover](cell-attachment-support/indexed-cone-open-cover.md)
- [The boundary of the two-disk is the circle](cell-attachment-support/disk-boundary-two-circle.md)
- [The degree-n circle map sends the generator to the degree-n loop](cell-attachment-support/circle-degree-map.md)
- [An indexed cone attachment is a standard cell attachment](cell-attachment-support/indexed-basic-cell-attachment.md)
- [Attaching 2-cells adds the attaching relations](attach-two-cells-fundamental-group.md)
- [The degree-n circle relation gives the cyclic group](cell-attachment-support/cyclic-relation-quotient.md)

## Sources

- [Hatcher §1.2, Example 1.29](../../../sources/hatcher-1-2.md)
