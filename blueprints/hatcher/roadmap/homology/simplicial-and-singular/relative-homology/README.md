---
article_id: af_a43e897716ffaf6560f50495
---

# Relative homology and exact sequences

Hatcher §2.1 (pages 110, 113–118, and 127–128). This selected slice introduces
reduced homology from the augmented singular complex, relative homology of a
topological pair, the long exact sequence of a pair, homotopy invariance, and
naturality.

The mathematical source is Hatcher. The representation against Mathlib is
fixed separately in the
[project-authored implementation specification](../../../../sources/relative-homology-implementation.md).
The pair branch is gated on a stable Mathlib pin containing the `SSetPair`
relative-homology API merged in PR #41285; the reduced branch and the generic
long exact sequence can be implemented against the current pin.

## Reduced homology

- [The augmented singular chain complex](augmented-singular-chain-complex.md)
- [Reduced singular homology](reduced-singular-homology.md)
- [Reduced and ordinary homology agree in positive degrees](reduced-positive-degree-comparison.md)
- [Zeroth homology splits into reduced homology and the coefficient object](pointed-zeroth-homology-splitting.md)

## Relative chains and homology

- [Relative homology of a simplicial-set pair](simplicial-pair-relative-homology.md)
- [The singular set of a topological pair](singular-pair-functor.md)
- [Relative singular chains and homology](relative-singular-homology.md)

## Exact sequences and homotopy invariance

- [A short exact sequence gives an exact homology sequence](short-exact-homology-sequence.md)
- [The long exact sequence of a pair](pair-long-exact-sequence.md)
- [The pair long exact sequence is natural](pair-long-exact-sequence-naturality.md)
- [A homotopy of pairs gives a relative chain homotopy](relative-singular-chain-homotopy.md)
- [Homotopic maps of pairs induce the same relative-homology map](relative-homology-homotopy-invariance.md)
- [The reduced long exact sequence of a nonempty pair](reduced-pair-long-exact-sequence.md)
- [The reduced pair long exact sequence is natural](reduced-pair-long-exact-sequence-naturality.md)
- [Relative homology at a basepoint is reduced homology](pointed-relative-reduced-homology.md)

## Deferred boundary

Theorem 2.13, Example 2.17, the triple sequence, excision and small chains,
good-pair quotient comparison, sphere applications, invariance of dimension,
and the simplicial–singular comparison remain deferred.

## Sources

- [Hatcher §2.1](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
