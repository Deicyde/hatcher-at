---
article_id: af_28607389cd096a6a3db5da9a
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
---

# Every fundamental-group element has a based disk-boundary representative

For a pointed topological space `(X, x₀)` and
`g : FundamentalGroup X x₀`, construct a continuous map from the boundary of
the standard two-disk to `X`, preserving the chosen basepoints and sending the
standard positively oriented boundary loop to `g`.

Intended main artifact:

```lean
noncomputable def Hatcher.diskBoundaryMapOfFundamentalGroup
    {X : Type u} [TopologicalSpace X] {x₀ : X}
    (g : FundamentalGroup X x₀) :
    C(((TopCat.diskBoundary.{u} 2 : TopCat.{u}) : Type u), X)
```

The public API must include the basepoint simp lemma and:

```lean
theorem Hatcher.diskBoundaryMapOfFundamentalGroup_generator
    (g : FundamentalGroup X x₀) :
    FundamentalGroup.mapOfEq (diskBoundaryMapOfFundamentalGroup g)
      (diskBoundaryMapOfFundamentalGroup_basepoint g)
      (FundamentalGroup.fromPath (.mk diskBoundaryTwoLoop)) = g
```

A valid construction chooses a representative with `Quotient.out`, extends
its path to the unit interval, descends through `AddCircle`, and transports
along `diskBoundaryTwoHomeomorphCircle`.

## Depends on

- [The boundary of the two-disk is the circle](../cell-attachment-support/disk-boundary-two-circle.md)

## Sources

- [Hatcher §1.2, Proposition 1.26(a) and Corollary 1.28](../../../../sources/hatcher-1-2.md)
- [Presentation-complex implementation specification](../../../../sources/presentation-complex-implementation.md)
