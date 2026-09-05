---
declaration: theorem
origin: cited
not_ready: true
---

# The cyclic presentation complex

**Hatcher, Example 1.29 (page 52), group calculation only.** For a positive
natural number `n`, attach a 2-cell to `S¹` along the degree-`n` map. The
resulting presentation complex has fundamental group isomorphic to `ℤ/nℤ`.

Intended artifact: `Hatcher.fundamentalGroupEquiv_cyclicPresentationComplex`.

Before this theorem can be stated, define the concrete adjunction space, its
basepoint, and its degree-`n` attaching map. An arbitrary space realizing the
presentation `⟨x | xⁿ⟩` is not enough: Hatcher's example identifies the group
of this specific one-cell attachment. Mathlib's abstract `AttachCells` data
does not currently supply that point-set space or the open-cover geometry used
by the attachment theorem, so this node remains not ready.

The quotient calculation after the geometric step is already formalized in
[The degree-n circle relation gives the cyclic group](cell-attachment-support/cyclic-relation-quotient.md).

This node does not claim the example's later geometric assertions identifying
the `n = 2` case with `ℝP²` or excluding embeddings and surface structures for
higher `n`.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [Attaching 2-cells adds the attaching relations](attach-two-cells-fundamental-group.md)
- [The degree-n circle map sends the generator to the degree-n loop](cell-attachment-support/circle-degree-map.md)
- [The degree-n circle relation gives the cyclic group](cell-attachment-support/cyclic-relation-quotient.md)

## Sources

- [Hatcher §1.2, Example 1.29](../../../sources/hatcher-1-2.md)
