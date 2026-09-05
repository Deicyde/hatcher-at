---
article_id: af_e1a364ab3eaebce2e62114e0
source_units: [hatcher-1-2-selected-spine]
declaration: corollary
origin: cited
---

# Every group is a fundamental group

**Hatcher, Corollary 1.28 (page 52).** For every group `G`, there is a
two-dimensional cell complex `X_G` with `π₁(X_G) ≃* G`.

Intended artifact: `Hatcher.exists_twoDimensionalCWComplex_fundamentalGroupEquiv`.

The source-facing Lean statement should be equivalent to:

```lean
theorem exists_twoDimensionalCWComplex_fundamentalGroupEquiv
    (G : Type u) [Group G] :
    ∃ (X : TopCat.{u}) (x₀ : X) (c : TopCat.CWComplex X),
      (∀ γ : HomotopicalAlgebra.RelativeCellComplex.Cells c, γ.j ≤ 2) ∧
        Nonempty (FundamentalGroup X x₀ ≃* G)
```

Use the generator type of a presentation of `G` to form a wedge of circles,
then attach one 2-cell for each relator. The statement is for arbitrary groups,
not only finitely presented groups.

This corollary is algebraic once the presentation-complex realization theorem
is available: choose the presentation supplied by
`Hatcher.exists_presentedGroup_equiv`, realize it geometrically, and compose
the two group equivalences. It should not reconstruct the wedge or attachment
geometry itself.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [Every group admits a generators-and-relations presentation](every-group-presentation.md)
- [Presented groups have two-dimensional presentation complexes](presentation-complex-realization.md)

## Sources

- [Hatcher §1.2, Corollary 1.28](../../../sources/hatcher-1-2.md)
