---
article_id: af_94c9b10f3bfd64e882b0e386
declaration: def
origin: bridged
statement: formalized
lean: Hatcher.Sphere.sphereBallPinch, Hatcher.Sphere.sphereBallCenter, Hatcher.Sphere.sphereBallEmbedding, Hatcher.Sphere.sphereBallClosed, Hatcher.Sphere.sphereBallOpen, Hatcher.Sphere.sphereBallUnion, Hatcher.Sphere.SphereBallPinchData, Hatcher.Sphere.SphereBallPinchData.pinchMap, Hatcher.Sphere.SphereBallPinchData.pinch_map_apply_ball, Hatcher.Sphere.SphereBallPinchData.pinch_map_apply_compl, Hatcher.Sphere.SphereBallPinchData.summandSelector, Hatcher.Sphere.SphereBallPinchData.summand_selector_apply_basepoint, Hatcher.Sphere.SphereBallPinchData.summand_selector_apply_inclusion, Hatcher.Sphere.SphereBallPinchData.componentCollapse, Hatcher.Sphere.SphereBallPinchData.component_collapse_apply_ball, Hatcher.Sphere.SphereBallPinchData.component_collapse_apply_other, Hatcher.Sphere.SphereBallPinchData.component_collapse_apply_compl, Hatcher.Sphere.SphereBallPinchData.component_collapse_apply_not_mem, Hatcher.Sphere.SphereBallPinchData.pinch_map_zero, Hatcher.Sphere.SphereBallPinchData.emptyWedgeToSphere, Hatcher.Sphere.SphereBallPinchData.emptySphereMap, Hatcher.Sphere.SphereBallPinchData.empty_sphere_map_eq_const
---

# Collapsing the complement of disjoint sphere balls gives the pinch map

For the constructed ball family in Sⁿ, identify the actual quotient Sⁿ/(Sⁿ−⋃ᵢ Bᵢ) with the pointed wedge of k copies of Sⁿ, each based at b. Define its quotient projection q : Sⁿ → ⋁ₖ Sⁿ.

## Proof sketch

On each Bᵢ the projection is the ith inclusion composed with a homeomorphism Bᵢ ≃ Sⁿ−{b}; outside their union it is the wedge point. Compose with the map selecting the ith summand and collapsing all others to b to obtain the continuous component collapse cᵢ : Sⁿ → Sⁿ. Expose the actual formulas and retain k = 0.

## Depends on

- [A positive-dimensional sphere contains any finite number of disjoint balls](finite-disjoint-sphere-balls.md)
- [point quotient functor](../../../simplicial-and-singular/relative-homology/good-pair-quotient/point-quotient-functor.md)
- [pointed wedge](../../../../fundamental-group/van-kampen/pointed-wedge.md)

## Proof depends on

- [Collapsing a compact complement gives a one-point compactification](compact-complement-quotient-one-point.md)
- [Compactifying a finite disjoint union gives the pointed wedge](finite-one-point-sigma-wedge.md)
- [disjoint open union homeomorphism](../../local-degree/disjoint-open-union-homeomorphism.md)
- [punctured sphere stereographic](../../degree/punctured-sphere-stereographic.md)

## Sources

- [Hatcher §2.2, printed pages 136–137](../../../../../sources/hatcher-2-2-degree-applications.md#example-231)
- [Degree-realization and suspension specification](../../../../../sources/degree-applications-implementation.md)
