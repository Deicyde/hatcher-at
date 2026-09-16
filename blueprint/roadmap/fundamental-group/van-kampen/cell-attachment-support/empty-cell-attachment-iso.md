---
article_id: af_9d7266d5983f276518daca8e
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
---

# An attachment with no cells is an isomorphism

For `c : HomotopicalAlgebra.AttachCells.{u}
(TopCat.RelativeCWComplex.basicCell n) f` with an empty cell-index type, show
that the attachment map `f` is an isomorphism in `TopCat`.

Intended artifact: `Hatcher.VanKampen.CellAttachment.targetIsoOfIsEmpty`.
Compose the abstract-to-indexed model isomorphism with the homeomorphism from
an empty indexed cone attachment to its base. This is the degenerate branch of
Proposition 1.26; it must not be handled by adding a dummy apex to Hatcher's
nonempty connected cover.

## Depends on

- [Every abstract cell attachment has an indexed cone model](abstract-cell-attachment-indexed-model.md)
- [An indexed family of cones has a two-set open cover](indexed-cone-open-cover.md)

## Sources

- [Hatcher §1.2, Proposition 1.26](../../../../sources/hatcher-1-2.md)
