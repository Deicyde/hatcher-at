---
article_id: af_ce0cbfdf3fed16c8fe605273
source_units: [hatcher-2-2-degree-foundations]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Sphere.integralSphereHomologyIso
---

# The ordered class orients ordinary sphere homology

For `n : ℕ` with `0 < n`, construct the integral isomorphism

```lean
noncomputable def Hatcher.Sphere.integralSphereHomologyIso
    (n : ℕ) (hn : 0 < n) :
    (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).obj (TopCat.sphere.{0} n)) ≅
      AddCommGrpCat.of ℤ
```

Its inverse is the ordinary fundamental class obtained from
`Hatcher.Simplex.doubleSimplexSphereFundamentalClass` through the natural
positive-degree comparison between reduced and ordinary homology. Record the
class and prove that it is an isomorphism. The orientation must therefore be
the completed ordered double-simplex orientation, not an arbitrary choice.

The named class is
`Hatcher.Sphere.integralSphereFundamentalClass`. The theorem
`Hatcher.Sphere.integralSphereHomologyIso_inv` identifies it exactly with the
inverse of the displayed isomorphism, while
`Hatcher.Sphere.integralSphereFundamentalClass_isIso` records that it is a
generator. Thus the ordinary orientation retains the order of the two
simplex summands used in Example 2.23.

## Depends on

- [The double simplex is a sphere](../post-excision-applications/double-simplex-sphere-homeomorphism.md)
- [Reduced and ordinary homology agree in positive degrees](../../simplicial-and-singular/relative-homology/reduced-positive-degree-comparison.md)

## Sources

- [Hatcher §2.2, definition of degree, printed page 134](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
