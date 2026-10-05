---
article_id: af_71d7ceb0f3904f7453776fe2
source_units: [hatcher-2-2-degree-foundations]
declaration: theorem
origin: cited
---

# A sphere reflection has degree minus one

For a unit normal vector `v`, define the Euclidean reflection of `Sⁿ` across
the equatorial subsphere orthogonal to `v`. It fixes that equator pointwise
and interchanges the two complementary hemispheres. For `0 < n`, prove

```lean
theorem Hatcher.Sphere.degree_reflection ... :
  degree n hn (reflectionIso n v).hom = -1
```

Compute the last-coordinate reflection by transporting the double-simplex
swap formula and its negation of the named class. Prove that an orthogonal
change of coordinates carries an arbitrary unit normal to the last coordinate,
then use conjugacy and multiplicativity of degree. Record every coordinate
reflection as a specialization for the antipodal factorization.

## Depends on

- [Degree is the multiplier of the ordered sphere class](sphere-degree-definition.md)
- [Coordinate sign changes on the sphere](sphere-coordinate-sign-changes.md)

## Proof depends on

- [The formal properties of degree](basic-degree-properties.md)

## Sources

- [Hatcher §2.2, degree property (e), printed page 134](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
