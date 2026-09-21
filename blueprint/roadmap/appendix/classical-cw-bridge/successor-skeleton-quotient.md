---
article_id: af_83ffc141377e9db9715f7e9e
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
---

# A successor classical skeleton has the cell-attachment quotient topology

Assemble the inclusion of `skeletonLT C n` and the restricted characteristic
maps of all classical `n`-cells into the joint map onto
`skeletonLT C (n + 1)`.

Intended main artifact:

```lean
theorem Hatcher.ClassicalCW.skeletonLTStepJointMap_isQuotient
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) {D : Set X} [Topology.RelCWComplex C D] (n : ℕ) :
    Topology.IsQuotientMap
      (Hatcher.ClassicalCW.skeletonLTStepJointMap C n)
```

The domain is the sum of the old skeleton and the sigma type of closed
sup-norm balls indexed by `Topology.RelCWComplex.cell C n`. Also expose the
coproduct boundary and closed-cell cofans, their commuting square, and a
successor-stage descent map with simp lemmas on the old skeleton and each
cell.

Prove surjectivity from
`skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ`. Prove the coinducing
direction using the inherited CW structure on the successor skeleton,
`RelCWComplex.closed`, and closedness of compact closed-cell images in the
Hausdorff ambient space. The underlying set-level pushout and its compatibility
with the attaching identifications are internal lemmas of this node.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2 bridge specification](../../../sources/classical-abstract-cw-bridge.md)
- [Mathlib's classical CW API](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Topology/CWComplex/Classical/Basic.lean)
- [Unmerged forward-bridge prior art](https://github.com/robertmaxton42/mathlib4/commit/0fef4116bba65c7017f7c3298ab1bc6d48afaded)
