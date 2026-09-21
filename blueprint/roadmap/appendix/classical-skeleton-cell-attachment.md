---
article_id: af_273a5ce6a092b8f64f470004
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
---

# Classical skeleton inclusions are abstract cell attachments

For a classical Mathlib CW complex, package the inclusion from one strict
skeleton to the next as a standard categorical cell attachment.

Intended main artifact:

```lean
noncomputable def Hatcher.ClassicalCW.skeletonLTInclusion_attachCells
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) {D : Set X} [Topology.RelCWComplex C D] (n : ℕ) :
    HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} n)
      (Hatcher.ClassicalCW.skeletonLTInclusion C n)
```

First turn the successor-stage quotient theorem into a `TopCat` pushout for
the coproduct of classical sup-norm cells. Then transport the cell family
along `classicalCellArrowIso` with `AttachCells.reindexCellTypes`. Also expose
the wrapper
`Hatcher.ClassicalCW.skeletonInclusion_attachCells C n`, whose cells have
dimension `n + 1` and whose underlying map is
`CWComplex.skeleton C n → CWComplex.skeleton C (n + 1)`.

This is the one-stage bridge needed by Hatcher's Proposition 1.26(c). It does
not construct a full abstract CW structure from a classical one. Mathlib
documents that broader comparison as a TODO and provides no bridge in the
pinned revision.

## Depends on

- [Classical and standard cells have isomorphic attaching arrows](classical-cw-bridge/classical-cell-arrow-iso.md)
- [A successor classical skeleton has the cell-attachment quotient topology](classical-cw-bridge/successor-skeleton-quotient.md)

## Sources

- [Hatcher §1.2 bridge specification](../../sources/classical-abstract-cw-bridge.md)
- [Mathlib abstract CW-complex implementation notes](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Topology/CWComplex/Abstract/Basic.lean)
