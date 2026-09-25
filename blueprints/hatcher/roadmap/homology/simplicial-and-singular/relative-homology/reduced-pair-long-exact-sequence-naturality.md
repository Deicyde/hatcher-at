---
article_id: af_d988056a42cddea384f57669
source_units: [hatcher-2-1-relative-homology-les]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Relative.reducedPairConnecting_naturality
---

# The reduced pair long exact sequence is natural

**Hatcher, §2.1 (pages 127–128).** A map of topological pairs with nonempty
subspaces induces a morphism between their reduced long exact homology
sequences, commuting in particular with the connecting homomorphisms.

`Hatcher.Relative.reducedPairSequenceMap` packages the induced morphism between
six consecutive terms. The main theorem
`Hatcher.Relative.reducedPairConnecting_naturality` proves the connecting
square directly from the natural augmented-chain construction, including in
degree zero. It does not transport naturality through a chosen-point splitting
of zeroth homology, since that splitting is not natural for unpointed spaces.

## Depends on

- [The reduced long exact sequence of a nonempty pair](reduced-pair-long-exact-sequence.md)

## Proof depends on

- [The pair long exact sequence is natural](pair-long-exact-sequence-naturality.md)
- [The augmented singular chain complex](augmented-singular-chain-complex.md)
- [A short exact sequence gives an exact homology sequence](short-exact-homology-sequence.md)

## Sources

- [Hatcher §2.1, naturality of the reduced pair sequence, pages 127–128](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
