---
article_id: af_a5d8f1242fb4422fcba20d43
source_units: [hatcher-2-2-degree-foundations]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Sphere.degree_eq_zero_of_not_surjective
---

# A nonsurjective sphere map has degree zero

For `0 < n` and `f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n`, prove

```lean
theorem Hatcher.Sphere.degree_eq_zero_of_not_surjective
    (hf : ¬ Function.Surjective f) :
    degree n hn f = 0
```

Choose a point outside the image, factor `f` through the punctured sphere,
and use its contractibility to show that the induced top-dimensional homology
map vanishes. The proof must identify the actual degree multiplier; merely
showing that some abstract endomorphism is zero is not the final statement.

The chosen missed
point gives an explicit `TopCat` factorization through its complement. The
published contractibility instance and positive-degree reduced-to-ordinary
comparison make the intermediate ordinary homology object zero, so the
conjugated integer endomorphism defining degree is literally the zero map.

## Depends on

- [Degree is the multiplier of the ordered sphere class](sphere-degree-definition.md)

## Proof depends on

- [A punctured sphere is Euclidean space](punctured-sphere-stereographic.md)
- [Reduced homology of a contractible space vanishes](../sphere-homology/contractible-space-reduced-homology.md)

## Sources

- [Hatcher §2.2, degree property (b), printed page 134](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
