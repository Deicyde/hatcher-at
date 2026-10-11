---
article_id: af_dad2eb4f720152d1a39ca44e
source_units: [hatcher-2-2-local-degree]
declaration: def
origin: bridged
---

# The ordered sphere class orients local homology

For `0 < n` and `y : TopCat.sphere n`, define

`Hatcher.Sphere.integralSphereLocalFundamentalClass n hn y`

with type

`AddCommGrpCat.of ℤ ⟶ H_n(puncturedPair (TopCat.sphere n) y; ℤ)`.

It is the completed ordered reduced sphere class followed by
`Hatcher.Relative.reducedPairProjection`.

The main artifact is the associated isomorphism
`Hatcher.Sphere.integralSphereLocalHomologyIso :`
`  H_n(Sⁿ,Sⁿ-{y};ℤ) ≅ AddCommGrpCat.of ℤ`, whose inverse is exactly this
class. Prove that both the ordered reduced sphere class and, by contractibility
of the punctured sphere, `reducedPairProjection` are isomorphisms. Pin the sign
by proving that the ordinary ordered class followed by the inverse
positive-degree reduced-to-ordinary comparison and then
`reducedPairProjection (puncturedPair Sⁿ y)` is exactly the local class.

For every open neighborhood `U` of `x`, also define the transported source
class `localClass(U,x) : ℤ ⟶ H_n(U,U-{x};ℤ)` as the unique class whose image
under the canonical open-neighborhood isomorphism is the global local class.
Prove this transported
class is an isomorphism. For nested open neighborhoods `V ⊆ U` containing
`x`, define the canonical morphism of punctured neighborhood pairs, prove that
it composes with the `U → Sⁿ` inclusion to the `V → Sⁿ` inclusion, and prove
the oriented restriction equation

`localClass(V,x) ≫ H_n(V → U) = localClass(U,x)`.

## Depends on

- [The ordered class orients ordinary sphere homology](../degree/integral-sphere-orientation.md)
- [A punctured sphere is Euclidean space](../degree/punctured-sphere-stereographic.md)
- [A contractible subspace compares relative and reduced homology](../post-excision-applications/contractible-subspace-relative-reduced-homology.md)

## Sources

- [Hatcher §2.2, local orientation in the definition of local degree, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
