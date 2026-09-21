---
article_id: af_bdf4b6a0596bcc5d303eeaf9
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
---

# Higher-cell attachments preserve path components

Attaching an arbitrary family of cells of one fixed dimension greater than one
does not merge path components of the source.

Intended main artifact:

```lean
theorem Hatcher.joined_iff_of_attachCells_of_one_lt
    {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (hn : 1 < n) (x y : X) :
    Joined (f x) (f y) ↔ Joined x y
```

Also provide `Hatcher.pathConnectedSpace_of_attachCells_of_two_lt`: if `X` is
path-connected and `2 < n`, then `Y` is path-connected. No finiteness
assumption on the cell index is allowed.

Transport the target to the explicit indexed-cone model. Radial paths join
every disk point to its nonempty boundary, while path-connectedness of
`TopCat.diskBoundary n` for `1 < n` shows that one attached disk cannot join
distinct source components. Establish the reverse implication for paths whose
endpoints lie in the base, not only the easier forward path-connectedness
corollary. Treat an empty cell family through the existing target isomorphism.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [Every abstract cell attachment has an indexed cone model](abstract-cell-attachment-indexed-model.md)
- [An attachment with no cells is an isomorphism](empty-cell-attachment-iso.md)

## Sources

- [Hatcher §1.2, induction in Proposition 1.26(c)](../../../../sources/hatcher-1-2.md)
- [Classical-to-abstract bridge specification](../../../../sources/classical-abstract-cw-bridge.md)
