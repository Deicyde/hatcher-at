---
article_id: af_65cb9c02fe8911d8b404bb3b
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.pointAttachCells
---

# A point is one standard zero-cell

Equip the unique map from the initial topological space to a point with one
standard zero-cell attachment.

Intended artifact:

```lean
noncomputable def Hatcher.VanKampen.pointAttachCells :
    HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} 0)
      (CategoryTheory.Limits.initial.to (TopCat.of PUnit.{u + 1}))
```

The cell index must be definitionally `PUnit`, or accompanied by a specified
equivalence with `PUnit`. Identify `TopCat.diskBoundary 0` with the empty
space and `TopCat.disk 0` with a point, then transport the one-index cone
attachment through the resulting source and target isomorphisms.

## Depends on

- [An indexed cone attachment is a standard cell attachment](../cell-attachment-support/indexed-basic-cell-attachment.md)

## Sources

- [Hatcher §1.2, proof of Corollary 1.28](../../../../sources/hatcher-1-2.md)
- [Presentation-complex implementation specification](../../../../sources/presentation-complex-implementation.md)
