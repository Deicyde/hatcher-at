---
article_id: af_48c015e1354062483f49ed29
source_units: [hatcher-2-2-degree-foundations]
declaration: theorem
origin: cited
---

# The antipodal map has degree determined by dimension

Factor the antipodal homeomorphism of `Sⁿ` into the `n+1` coordinate
reflections and prove, for `0 < n`,

```lean
theorem Hatcher.Sphere.degree_antipodal ... :
  degree n hn (antipodalIso n).hom = (-1 : ℤ) ^ (n + 1)
```

The factorization must be an equality of the explicit coordinate sign-change
maps, so multiplicativity of degree applies without an unspecified homotopic
replacement.

## Depends on

- [Coordinate sign changes on the sphere](sphere-coordinate-sign-changes.md)

## Proof depends on

- [The formal properties of degree](basic-degree-properties.md)
- [A sphere reflection has degree minus one](coordinate-reflection-degree.md)

## Sources

- [Hatcher §2.2, degree property (f), printed page 134](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
