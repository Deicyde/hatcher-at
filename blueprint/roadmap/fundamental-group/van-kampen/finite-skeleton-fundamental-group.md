---
article_id: af_3c10e2334ea23d186e4a5f3b
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.ClassicalCW.fundamentalGroupEquiv_twoSkeleton_skeleton
---

# Finite skeleta above dimension two have the same fundamental group

For every finite `m ≥ 2`, compose the equivalences induced by the successive
classical skeleton inclusions to identify the fundamental group of the
2-skeleton with that of the `m`-skeleton.

Intended main artifact:

```lean
noncomputable def Hatcher.ClassicalCW.fundamentalGroupEquiv_twoSkeleton_skeleton
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C] [PathConnectedSpace C]
    (m : ℕ) (hm : 2 ≤ m)
    (x₀ : Topology.CWComplex.skeleton C (2 : ℕ∞)) :
    FundamentalGroup (Topology.CWComplex.skeleton C (2 : ℕ∞)) x₀ ≃*
      FundamentalGroup (Topology.CWComplex.skeleton C (m : ℕ∞))
        ⟨x₀.1, Topology.CWComplex.skeleton_mono
          (C := C) (Nat.cast_le.mpr hm) x₀.2⟩
```

Also prove an application lemma identifying this equivalence with
`FundamentalGroup.map` for the direct subtype inclusion. Induct from dimension
two. At each successor, use the standard-cell attachment supplied by the
classical bridge, apply the higher-cell fundamental-group equivalence, and
propagate path-connectedness to the next skeleton. The base case is the
identity equivalence, and all basepoint transports must be explicit.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [Classical skeleton inclusions are abstract cell attachments](../../appendix/classical-skeleton-cell-attachment.md)
- [The 2-skeleton of a path-connected CW complex is path-connected](cell-attachment-support/path-connected-two-skeleton.md)
- [Attaching higher cells preserves the fundamental group](attach-higher-cells-fundamental-group.md)
- [Higher-cell attachments preserve path components](cell-attachment-support/higher-cell-attachment-path-components.md)

## Sources

- [Hatcher §1.2, finite-dimensional step in Proposition 1.26(c)](../../../sources/hatcher-1-2.md)
- [Classical-to-abstract bridge specification](../../../sources/classical-abstract-cw-bridge.md)
