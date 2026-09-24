---
article_id: af_1e6f9ec346e3b7485e19d9a3
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.ClassicalCW.classicalCellArrowIso
---

# Classical and standard cells have isomorphic attaching arrows

Compare the sup-norm disk-boundary inclusion used by Mathlib's classical
characteristic maps with the `ULift`ed L2 disk-boundary inclusion used by
`TopCat.RelativeCWComplex.basicCell`.

Intended main artifact:

```lean
noncomputable def Hatcher.ClassicalCW.classicalCellArrowIso (n : ℕ) :
    Arrow.mk (Hatcher.ClassicalCW.classicalDiskBoundaryInclusion.{u} n) ≅
      Arrow.mk (TopCat.RelativeCWComplex.basicCell.{u} n ())
```

Define the universe-lifted classical disk, boundary, and inclusion as
supporting interfaces. Use `WithLp.linearEquiv` for the ambient topological
linear equivalence and
`exists_homeomorph_image_interior_closure_frontier_eq_unitBall` for radial
gauge rescaling. Restrict the result to the unit closed balls and spheres, then
prove that the two restrictions commute with inclusion. The construction must
include `n = 0`; a linear homeomorphism alone is insufficient because it need
not preserve the two unit spheres.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2 bridge specification](../../../sources/classical-abstract-cw-bridge.md)
- [Mathlib's standard cell family](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Topology/CWComplex/Abstract/Basic.lean)
