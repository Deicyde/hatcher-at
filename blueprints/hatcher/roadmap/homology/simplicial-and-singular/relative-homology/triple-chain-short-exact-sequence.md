---
article_id: af_f2cf9ea8b806c2c89d563079
source_units: [hatcher-2-1-triple-les]
declaration: theorem
origin: bridged
---

# Relative chains of a triple form a short exact sequence

For a topological triple `(X,A,B)` and coefficients `R`, the canonical maps of
relative singular chain complexes form a short exact sequence

`0 → C_*(A,B;R) → C_*(X,B;R) → C_*(X,A;R) → 0`.

The main theorem `Hatcher.Relative.tripleChainComplexShortComplex_shortExact`
proves short exactness. The short complex itself and its functorial maps are
supporting declarations. Its proof uses the cokernel tail of Mathlib's
`kernelCokernelCompSequence` and the existing universal properties of relative
chains, rather than copying the unmerged basis-splitting implementation from
Mathlib PR #41318.

## Depends on

- [Topological triples and their maps](topological-triple.md)
- [Relative singular chains and homology](relative-singular-homology.md)

## Proof depends on

- [Relative homology of a simplicial-set pair](simplicial-pair-relative-homology.md)

## Sources

- [Hatcher §2.1, triple chain sequence, pages 118–119](../../../../sources/hatcher-2-1.md)
- [Triple-homology implementation specification](../../../../sources/triple-homology-implementation.md)
