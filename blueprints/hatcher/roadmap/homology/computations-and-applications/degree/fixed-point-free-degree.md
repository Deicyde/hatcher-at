---
article_id: af_c2fff585a63bdde52a391759
source_units: [hatcher-2-2-degree-foundations]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Sphere.degree_eq_neg_one_pow_of_fixedPointFree
---

# A fixed-point-free sphere map has antipodal degree

Let `0 < n` and `f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n`. Under
`hf : ∀ x, f x ≠ x`, construct Hatcher's homotopy obtained by normalizing

`(1-t)f(x) - tx`.

Prove that the unnormalized vector never vanishes, that normalization remains
on the unit sphere, and that the endpoints are `f` and the antipodal map.
The main source-facing conclusion is

```lean
theorem Hatcher.Sphere.degree_eq_neg_one_pow_of_fixedPointFree ... :
  degree n hn f = (-1 : ℤ) ^ (n + 1)
```

Taking norms of a hypothetical zero of the unnormalized segment forces its
two coefficients to agree and be nonzero, so scalar cancellation would make
`f(x)=x`. This proves normalization is continuous on the whole cylinder. Its
endpoints are the original map and the completed explicit antipodal
isomorphism, and homotopy invariance transports the antipodal degree formula
to `f`.

## Depends on

- [Degree is the multiplier of the ordered sphere class](sphere-degree-definition.md)

## Proof depends on

- [The formal properties of degree](basic-degree-properties.md)
- [The antipodal map has degree determined by dimension](antipodal-degree.md)

## Sources

- [Hatcher §2.2, degree property (g), printed pages 134–135](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
