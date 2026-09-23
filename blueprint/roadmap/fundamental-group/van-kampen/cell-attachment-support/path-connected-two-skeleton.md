---
article_id: af_5fb3ca54030c6288d4ce8eea
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.ClassicalCW.pathConnectedSpace_twoSkeleton
---

# The 2-skeleton of a path-connected CW complex is path-connected

Supply the path-connectedness instance required before iterating the
higher-cell fundamental-group theorem from the classical 2-skeleton.

Intended main artifact:

```lean
theorem Hatcher.ClassicalCW.pathConnectedSpace_twoSkeleton
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C] [PathConnectedSpace C] :
    PathConnectedSpace (Topology.CWComplex.skeleton C (2 : ℕ∞))
```

For two points of the 2-skeleton, choose a path between them in `C`. Its image
is compact, hence lies in a bounded skeleton. Work downward through the
finitely many higher dimensions. At each step, use the classical attachment
bridge and `joined_iff_of_attachCells_of_one_lt` to reflect joinedness across
the successor-skeleton inclusion. This proves the instance from ambient
path-connectedness; the theorem must not assume the 2-skeleton is
path-connected.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [Compact subsets lie in a bounded skeleton](../../../appendix/classical-cw-bridge/compact-subset-bounded-skeleton.md)
- [Classical skeleton inclusions are abstract cell attachments](../../../appendix/classical-skeleton-cell-attachment.md)
- [Higher-cell attachments preserve path components](higher-cell-attachment-path-components.md)

## Sources

- [Hatcher §1.2, proof of Proposition 1.26(c)](../../../../sources/hatcher-1-2.md)
- [Classical-to-abstract bridge specification](../../../../sources/classical-abstract-cw-bridge.md)
- [Hatcher Appendix Exercise 3, path components and the 1-skeleton](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf#page=538)
