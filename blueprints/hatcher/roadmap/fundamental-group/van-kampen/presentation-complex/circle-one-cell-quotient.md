---
article_id: af_6c25ed58fef0c56b0b6e98b9
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.circleOneCellHomeomorph
---

# Collapsing the boundary of a one-disk gives the circle

Attach the cone on `TopCat.diskBoundary 1` to a point by the unique map and
identify the resulting quotient with the circle, with the image of the point
corresponding to `1`.

Intended artifact:

```lean
noncomputable def Hatcher.VanKampen.circleOneCellHomeomorph :
    Hatcher.VanKampen.ConeAttachment
      (fun _ : ((TopCat.diskBoundary.{u} 1 : TopCat.{u}) : Type u) =>
        PUnit.unit) ≃ₜ ULift.{u} _root_.Circle
```

Also prove the simp lemma sending the cone-attachment basepoint to
`ULift.up (1 : Circle)`. Use the standard homeomorphisms from the one-disk to
a closed interval, from the interval quotient to `AddCircle`, and from
`AddCircle` to `Circle`. The `ULift` is required by the standard-cell
universe.

## Depends on

- [A single cone attachment has a two-set open cover](../cell-attachment-support/single-cone-open-cover.md)
- [The cone on a disk boundary is the disk](../cell-attachment-support/cone-disk-homeomorphism.md)

## Sources

- [Hatcher §1.2, proof of Corollary 1.28](../../../../sources/hatcher-1-2.md)
- [Presentation-complex implementation specification](../../../../sources/presentation-complex-implementation.md)
