---
article_id: af_82daa470562d75a3f2a999dd
source_units: [hatcher-2-2-degree-foundations]
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Sphere.nonvanishingTangentVectorFieldOfOdd
---

# Odd spheres have a nonvanishing tangent field

Given `Odd n`, pair the `n+1` ambient coordinates and define Hatcher's
quarter-turn field

`(x₁,x₂,…,x₂ₖ₋₁,x₂ₖ) ↦ (-x₂,x₁,…,-x₂ₖ,x₂ₖ₋₁)`.

Construct

```lean
noncomputable def Hatcher.Sphere.nonvanishingTangentVectorFieldOfOdd ... :
  TangentVectorField n
```

and prove that it has unit norm, hence is nowhere zero. The construction must
handle the coordinate reindexing explicitly and retain continuity as part of
the bundled field.

The public
`oddSphereCoordinateEquiv` and paired-coordinate equations expose the literal
quarter-turn formula, while
`nonvanishingTangentVectorFieldOfOdd_nonvanishing` proves the resulting field
is nowhere zero.

## Depends on

- [Tangent vector fields and normalization](tangent-vector-field-data.md)

## Sources

- [Hatcher §2.2, reverse implication of Theorem 2.28, printed page 135](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
