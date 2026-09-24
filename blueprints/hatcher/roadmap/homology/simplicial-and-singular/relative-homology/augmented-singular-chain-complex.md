---
article_id: af_7968fc65ae53f656ce78c58d
source_units: [hatcher-2-1-relative-homology-les]
declaration: def
origin: cited
lean: Hatcher.Reduced.augmentedSingularChainComplexFunctor
statement: formalized
---

# The augmented singular chain complex

**Hatcher, §2.1 (page 110).** For a space `X` and coefficient object `R`,
augment the singular chain complex by the map from degree-zero chains to `R`
that sends every singular zero-simplex to the identity of `R`.

The main artifact should be
`Hatcher.Reduced.augmentedSingularChainComplexFunctor`. Mathlib's
`ChainComplex.augment` shifts the ordinary singular complex up one degree, so
degree zero is `R` and degree `n + 1` is `Cₙ(X;R)`. Supporting declarations
construct the natural chain-level augmentation and prove that the degree-one
boundary followed by it is zero.

The construction is coefficient-general in an abelian category with the
required coproducts. Hatcher's complex is its integral specialization. The
functor may be defined for the empty space as well; the roadmap's
nonnegative-degree groups then extend Hatcher's convention, which suppresses
the degree `-1` group by working with nonempty spaces.

## Depends on

- [The singular chain complex](../singular-chain-complex.md)

## Sources

- [Hatcher §2.1, reduced homology, page 110](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
