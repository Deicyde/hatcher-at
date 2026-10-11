---
article_id: af_dad2eb4f720152d1a39ca44e
source_units: [hatcher-2-2-local-degree]
declaration: def
origin: bridged
---

# The ordered sphere class orients local homology

For `0 < n` and `y : TopCat.sphere n`, define

`Hatcher.Sphere.integralSphereLocalFundamentalClass n hn y`

from `ℤ` to the degree-`n` relative homology of
`puncturedPair (TopCat.sphere n) y`. It is the completed ordered reduced sphere
class followed by `Hatcher.Relative.reducedPairProjection`.

The main artifact is the associated isomorphism
`Hatcher.Sphere.integralSphereLocalHomologyIso`, whose inverse is exactly this
class. Prove that the class is an isomorphism because the punctured sphere is
contractible, and record its naturality equation with the ordinary integral
sphere class through the positive-degree reduced-to-ordinary comparison.

For every open neighborhood `U` of `x`, also define the transported source
class in `H_n(U,U-{x};ℤ)` as the unique class whose image under the canonical
open-neighborhood isomorphism is the global local class. Prove this transported
class is an isomorphism and record its naturality under further restriction.

## Depends on

- [The ordered class orients ordinary sphere homology](../degree/integral-sphere-orientation.md)
- [A punctured sphere is Euclidean space](../degree/punctured-sphere-stereographic.md)
- [A contractible subspace compares relative and reduced homology](../post-excision-applications/contractible-subspace-relative-reduced-homology.md)

## Sources

- [Hatcher §2.2, local orientation in the definition of local degree, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
