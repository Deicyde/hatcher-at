---
article_id: af_096133707d4ba17fcfa64275
source_units: [hatcher-2-1-triple-les]
declaration: theorem
origin: cited
---

# The long exact sequence of a triple

**Hatcher, §2.1 (pages 118–119).** For nested subspaces `B ⊆ A ⊆ X`, the
relative groups fit into a natural long exact sequence

`⋯ → H_n(A,B;R) → H_n(X,B;R) → H_n(X,A;R)`
`→ H_{n-1}(A,B;R) → H_{n-1}(X,B;R) → ⋯`.

For adjacent degrees `m + 1 = n`, `Hatcher.Relative.tripleSequence` packages
six consecutive terms and `Hatcher.Relative.tripleSequence_exact` proves
exactness at every position. The same review unit exposes the connecting map
and the degree-zero epimorphism `H_0(X,B;R) → H_0(X,A;R)`.

## Depends on

- [Relative chains of a triple form a short exact sequence](triple-chain-short-exact-sequence.md)

## Proof depends on

- [A short exact sequence gives an exact homology sequence](short-exact-homology-sequence.md)

## Sources

- [Hatcher §2.1, triple long exact sequence, pages 118–119](../../../../sources/hatcher-2-1.md)
- [Triple-homology implementation specification](../../../../sources/triple-homology-implementation.md)
