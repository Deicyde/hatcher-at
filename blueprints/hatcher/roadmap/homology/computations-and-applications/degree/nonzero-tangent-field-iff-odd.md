---
article_id: af_f60a411fd48e65a2b5a72805
source_units: [hatcher-2-2-degree-foundations]
declaration: theorem
origin: cited
---

# A sphere has a nonvanishing tangent field exactly in odd dimension

Assemble the two directions of Hatcher's Theorem 2.28. For `0 < n`, prove

```lean
theorem Hatcher.Sphere.exists_nonvanishingTangentVectorField_iff_odd ... :
  (∃ v : TangentVectorField n, v.Nonvanishing) ↔ Odd n
```

The forward direction must use the identity-to-antipodal homotopy and the
oriented degree calculation. The reverse direction must return the explicit
paired-coordinate field, not merely a classical existence proof.

## Depends on

- [Tangent vector fields and normalization](tangent-vector-field-data.md)

## Proof depends on

- [A nonvanishing tangent field forces odd dimension](tangent-field-parity-obstruction.md)
- [Odd spheres have a nonvanishing tangent field](odd-sphere-tangent-field.md)

## Sources

- [Hatcher §2.2, Theorem 2.28, printed page 135](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
