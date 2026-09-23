---
article_id: af_759c634e0bfe5a36d279e9d0
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.presentationRelatorAttachCells
---

# Free-group relators form a standard two-cell attachment

For `rels : Set (FreeGroup S)`, realize each relator as a based map from the
boundary of a two-disk into the pointed wedge of `S` circles, and package the
family as an indexed attachment by standard two-cells.

The public API must include a based continuous map
`Hatcher.wedgeCircleRelatorAttachingMap r`, an indexed family
`Hatcher.presentationRelatorAttachingMap rels`, the resulting space
`Hatcher.presentationComplex rels` and its basepoint, and:

```lean
noncomputable def Hatcher.presentationRelatorAttachCells
    {S : Type u} (rels : Set (FreeGroup S)) :
    HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} 2)
      (Hatcher.presentationComplexBaseHom rels)
```

For every `r : rels`, prove that the corresponding attaching loop, transported
through `Hatcher.fundamentalGroupEquivWedgeCircles`, is exactly `r.1`. This
correctness theorem is the only representation detail the quotient
calculation may use.

## Depends on

- [Every fundamental-group element has a based disk-boundary representative](disk-boundary-fundamental-group-representative.md)
- [The fundamental group of a wedge of circles](../wedge-circles-free-group.md)
- [An indexed cone attachment is a standard cell attachment](../cell-attachment-support/indexed-basic-cell-attachment.md)
- [Attaching 2-cells adds the attaching relations](../attach-two-cells-fundamental-group.md)

## Sources

- [Hatcher §1.2, proof of Corollary 1.28, page 52](../../../../sources/hatcher-1-2.md)
- [Presentation-complex implementation specification](../../../../sources/presentation-complex-implementation.md)
