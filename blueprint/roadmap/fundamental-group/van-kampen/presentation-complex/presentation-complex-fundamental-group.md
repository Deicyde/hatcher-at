---
article_id: af_5ef0b19d3507e0f51deef27d
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.presentationComplexFundamentalGroupEquiv
---

# The presentation complex has the presented fundamental group

Compute the fundamental group of the concrete presentation complex by the
two-cell attachment theorem and transport the attaching normal closure through
the free-group equivalence for the wedge of circles.

Intended main artifact:

```lean
noncomputable def Hatcher.presentationComplexFundamentalGroupEquiv
    {S : Type u} (rels : Set (FreeGroup S)) :
    PresentedGroup rels ≃*
      FundamentalGroup (Hatcher.presentationComplex rels)
        (Hatcher.presentationComplexBasepoint rels)
```

Prove explicitly that mapping the normal closure of the attaching loops along
`Hatcher.fundamentalGroupEquivWedgeCircles` gives
`Subgroup.normalClosure rels`, then use `QuotientGroup.congr`. The result must
include empty and infinite presentations and must not assume a finitely
generated or finitely presented group.

## Depends on

- [Free-group relators form a standard two-cell attachment](relator-cell-attachment.md)
- [Pointed wedges of path-connected spaces are path-connected](pointed-wedge-path-connected.md)
- [The fundamental group of a wedge of circles](../wedge-circles-free-group.md)
- [Attaching 2-cells adds the attaching relations](../attach-two-cells-fundamental-group.md)

## Sources

- [Hatcher §1.2, proof of Corollary 1.28, page 52](../../../../sources/hatcher-1-2.md)
- [Presentation-complex implementation specification](../../../../sources/presentation-complex-implementation.md)
