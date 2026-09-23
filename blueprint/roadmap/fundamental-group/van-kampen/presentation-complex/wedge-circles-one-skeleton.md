---
article_id: af_f504a5652653f883d78795e8
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.wedgeCirclesAttachCells
---

# A wedge of circles is an indexed one-cell attachment

Equip the map from a point to the common basepoint of a wedge of circles with
one standard one-cell for each circle.

Intended artifacts:

```lean
def Hatcher.wedgeCirclesBaseHom {ι : Type u} :
    TopCat.of PUnit.{u + 1} ⟶
      TopCat.of (Hatcher.PointedWedge
        (fun _ : ι => _root_.Circle) (fun _ => (1 : _root_.Circle)))

noncomputable def Hatcher.wedgeCirclesAttachCells {ι : Type u} :
    HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} 1)
      (Hatcher.wedgeCirclesBaseHom (ι := ι))
```

The attachment's cell index must be definitionally `ι`, or accompanied by a
specified equivalence with `ι`; the construction must include the empty-index
case. Build the indexed cone attachment for constant maps to `PUnit`, identify
each quotient summand with the circle, use the pointed-wedge universal
property to assemble the homeomorphism, and transport the existing
`AttachCells` structure through the resulting arrow isomorphism.

## Depends on

- [The pointed wedge of a family of spaces](../pointed-wedge.md)
- [Continuous maps out of a pointed wedge](pointed-wedge-universal-property.md)
- [Collapsing the boundary of a one-disk gives the circle](circle-one-cell-quotient.md)
- [An indexed cone attachment is a standard cell attachment](../cell-attachment-support/indexed-basic-cell-attachment.md)

## Sources

- [Hatcher §1.2, proof of Corollary 1.28](../../../../sources/hatcher-1-2.md)
- [Presentation-complex implementation specification](../../../../sources/presentation-complex-implementation.md)
