---
article_id: af_d318cc4dc82968256f79aee5
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
---

# The identity attaches an empty family of cells

For every dimension and topological space, equip the identity map with a
standard cell-attachment structure whose cell index is `PEmpty`.

Intended artifact:

```lean
noncomputable def Hatcher.VanKampen.CellAttachment.attachCellsId
    (n : ℕ) (X : TopCat.{u}) :
    HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} n) (𝟙 X)
```

Construct both indexed coproducts as initial objects and use the identity
pushout square. The empty index must remain visible to the later dimension
bound.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2, proof of Corollary 1.28](../../../../sources/hatcher-1-2.md)
- [Presentation-complex implementation specification](../../../../sources/presentation-complex-implementation.md)
