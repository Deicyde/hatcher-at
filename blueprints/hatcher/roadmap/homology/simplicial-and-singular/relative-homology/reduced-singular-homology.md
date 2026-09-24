---
article_id: af_d419a29f857a10423aa75cdf
source_units: [hatcher-2-1-relative-homology-les]
declaration: def
origin: cited
---

# Reduced singular homology

**Hatcher, §2.1 (pages 110 and 113).** Define reduced singular homology
`Ḥₙ(X;R)` as degree `n + 1` homology of the augmented singular chain
complex. Continuous maps induce maps on these groups, giving a functor in the
space.

The main artifact should be `Hatcher.Reduced.homologyFunctor`. It must use the
augmented complex rather than define reduced homology through a chosen
basepoint; the latter is a theorem in Example 2.18. Defining the functor on the
empty space is harmless in the displayed nonnegative degrees and is recorded
as an extension of Hatcher's nonempty-space convention.

## Depends on

- [The augmented singular chain complex](augmented-singular-chain-complex.md)

## Sources

- [Hatcher §2.1, reduced homology and induced maps, pages 110 and 113](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
