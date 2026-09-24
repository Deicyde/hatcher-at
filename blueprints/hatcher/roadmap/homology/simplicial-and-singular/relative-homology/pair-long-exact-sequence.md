---
article_id: af_28eb45968cda0d7223634efb
source_units: [hatcher-2-1-relative-homology-les]
declaration: theorem
origin: cited
---

# The long exact sequence of a pair

**Hatcher, §2.1 (page 117).** For a topological pair `(X,A)`, the inclusion,
the map induced by the relative-chain quotient, and the connecting maps form
an exact sequence

`... → Hₙ(A;R) → Hₙ(X;R) → Hₙ(X,A;R) → Hₙ₋₁(A;R) → ...`.

The main artifact should be `Hatcher.Relative.pairSequence_exact`, uniformly
quantified over adjacent degrees. In the integral `AddCommGrp` specialization,
the connecting map must agree with the source's elementwise description: a
relative cycle represented by `α` is sent to the class of `∂α`.

## Depends on

- [Relative singular chains and homology](relative-singular-homology.md)
- [Singular homology](../singular-homology.md)

## Proof depends on

- [Relative homology of a simplicial-set pair](simplicial-pair-relative-homology.md)
- [A short exact sequence gives an exact homology sequence](short-exact-homology-sequence.md)

## Sources

- [Hatcher §2.1, pair exact sequence, page 117](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
