---
article_id: af_7da35d562938b0efe2922263
source_units: [hatcher-2-1-relative-homology-les]
declaration: def
origin: cited
---

# Reduced and ordinary homology agree in positive degrees

**Hatcher, §2.1 (page 110).** For every space `X`, coefficient object `R`,
and positive degree `n`, construct the natural isomorphism
`Ḥₙ(X;R) ≅ Hₙ(X;R)`.

The main artifact should be `Hatcher.Reduced.homologyIsoOfPositiveDegree`.
It is induced by the degree shift in `ChainComplex.augment`, not by choosing a
basepoint.

## Depends on

- [Reduced singular homology](reduced-singular-homology.md)
- [Singular homology](../singular-homology.md)

## Sources

- [Hatcher §2.1, reduced homology, page 110](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
