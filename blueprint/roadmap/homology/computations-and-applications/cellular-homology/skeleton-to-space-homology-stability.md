---
article_id: af_802fb71f8d9fa8e8806b6612
declaration: theorem
origin: cited
---

# The skeleton inclusion preserves homology below its dimension

**Hatcher, Lemma 2.34(c).** For every classical CW complex X, the actual
inclusion Xⁿ → X induces an isomorphism on Hₖ(−;ℤ) when k < n and a
surjection when k = n, hence also when k ≤ n. Include empty and
infinite-dimensional complexes and arbitrary cell sets.

## Proof sketch

Lift an actual cycle to a common higher skeleton and use finite-stage
surjectivity. For injectivity, lift a bounding chain to a higher skeleton,
reflect its boundary equation and use finite-stage injectivity. The result
uses finite support of chains, not finite dimension of X.

## Depends on

- [Singular homology](../../simplicial-and-singular/singular-homology.md)

## Proof depends on

- [Finite stage homology stability](finite-stage-homology-stability.md)
- [Singular chains bounded skeleton](singular-chains-bounded-skeleton.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)
