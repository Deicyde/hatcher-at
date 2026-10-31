---
article_id: af_15277fbc486e518fc1e1acf7
source_units: [hatcher-2-2-degree-realization-suspension]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Sphere.circlePowerMap_inversion_reflection_and_degree
---

# Circle inversion is the standard coordinate reflection

Identify the transported circle map P_{−1} with the standard reflection of S¹ that negates the imaginary, or second real, coordinate. Consequently its signed degree is −1.

## Proof sketch

On the complex unit circle inverse is complex conjugation. The completed real-coordinate homeomorphism identifies conjugation with this coordinate sign change, so the existing reflection-degree theorem applies to the actual P_{−1}.

## Depends on

- [Integer powers define continuous self-maps of the circle](integer-circle-power-map.md)
- [Degree is the multiplier of the ordered sphere class](../../degree/sphere-degree-definition.md)
- [sphere coordinate sign changes](../../degree/sphere-coordinate-sign-changes.md)

## Proof depends on

- [coordinate reflection degree](../../degree/coordinate-reflection-degree.md)

## Sources

- [Hatcher §2.2, printed pages 136–137](../../../../../sources/hatcher-2-2-degree-applications.md#example-232)
- [Degree-realization and suspension specification](../../../../../sources/degree-applications-implementation.md)
