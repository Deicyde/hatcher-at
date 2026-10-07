---
article_id: af_530dad8cebc4444a6d3714d4
source_units: [hatcher-2-2-degree-foundations]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Sphere.odd_of_nonvanishingTangentVectorField
---

# A nonvanishing tangent field forces odd dimension

For `0 < n`, normalize a nonvanishing tangent vector field and construct the
continuous homotopy

`(t,x) ↦ (cos(πt))x + (sin(πt))v(x)`

from the identity of `Sⁿ` to the antipodal map. Orthogonality and unit norm
must prove that the formula stays on the sphere. Comparing endpoint degrees
then yields the main result

```lean
theorem Hatcher.Sphere.odd_of_nonvanishingTangentVectorField ... : Odd n
```

The supporting declaration
`identityHomotopyAntipodalOfNonvanishingTangentVectorField` is the explicit
cosine--sine homotopy; its norm calculation uses the normalized field's unit
norm and its orthogonality to the ambient sphere point.

## Depends on

- [Tangent vector fields and normalization](tangent-vector-field-data.md)

## Proof depends on

- [The formal properties of degree](basic-degree-properties.md)
- [The antipodal map has degree determined by dimension](antipodal-degree.md)

## Sources

- [Hatcher §2.2, forward implication of Theorem 2.28, printed page 135](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
