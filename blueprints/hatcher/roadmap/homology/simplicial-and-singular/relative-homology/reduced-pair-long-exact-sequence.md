---
article_id: af_df93848f39d91ecc5e5fab42
source_units: [hatcher-2-1-relative-homology-les]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Relative.reducedPairSequence_exact
---

# The reduced long exact sequence of a nonempty pair

**Hatcher, §2.1 (page 118).** For a topological pair `(X,A)` with nonempty
subspace, replace the two absolute homology terms in the pair long exact
sequence by reduced homology while retaining the same relative groups. The
resulting sequence is exact in every degree.

`Hatcher.Relative.reducedPairSequence` packages six consecutive terms and
`Hatcher.Relative.reducedPairSequence_exact` proves their exactness. The
construction uses the short exact sequence of augmented subspace and ambient
chains together with the zero-augmented relative complex. For a chosen point
of the nonempty subspace, `Hatcher.Relative.reducedPairZeroSequence_exact`
also proves the terminal exact sequence
`H̃₀(A) → H̃₀(X) → H₀(X,A) → 0` directly from the augmentation.
The overlap lemmas identify these finite windows as one coherent sequence, and
`Hatcher.Relative.reducedPairLongExact` packages all exactness conclusions.

## Depends on

- [The long exact sequence of a pair](pair-long-exact-sequence.md)
- [Reduced and ordinary homology agree in positive degrees](reduced-positive-degree-comparison.md)
- [Zeroth homology splits into reduced homology and the coefficient object](pointed-zeroth-homology-splitting.md)

## Sources

- [Hatcher §2.1, reduced pair sequence, page 118](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
