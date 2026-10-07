---
article_id: af_1e83c364583b4ef47b8b0570
source_units: [hatcher-2-2-degree-foundations]
declaration: structure
origin: bridged
statement: formalized
lean: Hatcher.Sphere.TangentVectorField
---

# Tangent vector fields and normalization

Define `Hatcher.Sphere.TangentVectorField n` as a continuous ambient vector
field on `TopCat.sphere.{0} n` whose value at `x` is orthogonal to `x`. Define
`TangentVectorField.Nonvanishing` pointwise.

For a nonvanishing field, construct its normalized field and prove continuity,
orthogonality, unit norm, and equality of its zero set with that of the
original field. The representation must match Hatcher's ambient formula and
must not introduce a tangent-bundle dependency.

The public API also records the continuous ambient-point map, its unit
norm, pointwise nonvanishing, and preservation of both the zero set and
nonvanishing under normalization.

## Depends on

None.

## Sources

- [Hatcher §2.2, tangent-field convention in Theorem 2.28, printed page 135](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
