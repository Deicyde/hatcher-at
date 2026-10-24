---
article_id: af_6335225854364397e3a20e8f
source_units: [hatcher-2-2-degree-realization-suspension]
declaration: theorem
origin: cited
---

# Suspension preserves the signed degree of a sphere map

**Hatcher, Proposition 2.33.** For n > 0 and every continuous f : Sⁿ → Sⁿ, prove degree(Sf) = degree(f) using the existing ordinary integral degree in dimensions n+1 and n.

## Proof sketch

Transport the natural reduced boundary isomorphism through the ordered sphere orientations and the positive-degree reduced/ordinary comparison. The resulting automorphism of ℤ has a proved unit multiplier. Naturality makes the two degree multipliers commute with it, and cancelling that unit gives equality; its sign is not an extra premise. Iterating this result and the circle-power calculation gives the source's alternative construction of prescribed sphere degrees.

## Depends on

- [A sphere map induces its genuine suspension map](sphere-suspension-map.md)
- [sphere degree definition](../../degree/sphere-degree-definition.md)

## Proof depends on

- [The suspension boundary isomorphism intertwines the induced maps](sphere-suspension-boundary-naturality.md)
- [reduced positive degree comparison](../../../simplicial-and-singular/relative-homology/reduced-positive-degree-comparison.md)
- [integral sphere orientation](../../degree/integral-sphere-orientation.md)

## Sources

- [Hatcher §2.2, printed pages 136–137](../../../../../sources/hatcher-2-2-degree-applications.md#proposition-233)
- [Degree-realization and suspension specification](../../../../../sources/degree-applications-implementation.md)
