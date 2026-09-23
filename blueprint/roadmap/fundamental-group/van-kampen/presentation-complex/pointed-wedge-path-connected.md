---
article_id: af_566c2d0d935658850d39e13f
source_units: [hatcher-1-2-selected-spine]
declaration: instance
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.PointedWedge.instPathConnectedSpace
---

# Pointed wedges of path-connected spaces are path-connected

For a family of path-connected spaces, equip `Hatcher.PointedWedge` with a
`PathConnectedSpace` instance. Map a path from each summand point to its
chosen basepoint through the canonical inclusion, then join arbitrary wedge
points through the common wedge point. The proof must also cover an empty
index type, for which this project's pointed wedge is a one-point space.

Intended main artifact:

```lean
instance Hatcher.PointedWedge.instPathConnectedSpace
    {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (x₀ : ∀ i, X i) [∀ i, PathConnectedSpace (X i)] :
    PathConnectedSpace (Hatcher.PointedWedge X x₀)
```

## Depends on

- [The pointed wedge of a family of spaces](../pointed-wedge.md)

## Sources

- [Hatcher §1.2, Example 1.21](../../../../sources/hatcher-1-2.md)
- [Presentation-complex implementation specification](../../../../sources/presentation-complex-implementation.md)
