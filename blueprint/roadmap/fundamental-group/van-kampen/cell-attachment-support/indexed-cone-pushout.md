---
article_id: af_5672357a1dfa0c16481f12ce
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
---

# An indexed family of cone attachments is a topological pushout

For a family of continuous attaching maps `f j : S j → X`, bundle the maps
from the topological coproduct `Σ j, S j` to `X` and to the coproduct of the
retained cones `Σ j, ConeAttachment (id : S j → S j)`. The explicit indexed
cone quotient is their pushout in `TopCat`.

Intended artifact:
`Hatcher.VanKampen.IndexedConeAttachment.isPushout_indexedConeAttachment`.
The same module should expose the four maps in this square and the resulting
`HomotopicalAlgebra.AttachCells` structure for the indexed retained-cone cell
family. Use `TopCat.sigmaCofan` and `TopCat.sigmaCofanIsColimit`, and keep the
index and space universes equal in this first interface rather than hiding a
resizing assumption.

## Depends on

- [An indexed family of cones has a two-set open cover](indexed-cone-open-cover.md)

## Sources

- [Hatcher §1.2, disk attachments in Proposition 1.26](../../../../sources/hatcher-1-2.md)
- [Mathlib's `AttachCells` pushout interface](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/AlgebraicTopology/RelativeCellComplex/AttachCells.lean)
- [Mathlib's explicit `TopCat` coproduct](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Topology/Category/TopCat/Limits/Products.lean)
