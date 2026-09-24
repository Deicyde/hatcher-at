---
article_id: af_df93848f39d91ecc5e5fab42
source_units: [hatcher-2-1-relative-homology-les]
declaration: theorem
origin: cited
---

# The reduced long exact sequence of a nonempty pair

**Hatcher, §2.1 (page 118).** For a topological pair `(X,A)` with nonempty
subspace, replace the two absolute homology terms in the pair long exact
sequence by reduced homology while retaining the same relative groups. The
resulting sequence is exact in every degree.

The main artifact should be `Hatcher.Relative.reducedPairSequence_exact`.
Its degree-zero end must use the augmentation sequence explicitly; positive
degrees use the natural comparison between reduced and ordinary homology.

## Depends on

- [The long exact sequence of a pair](pair-long-exact-sequence.md)
- [Reduced and ordinary homology agree in positive degrees](reduced-positive-degree-comparison.md)
- [Zeroth homology splits into reduced homology and the coefficient object](pointed-zeroth-homology-splitting.md)

## Sources

- [Hatcher §2.1, reduced pair sequence, page 118](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
