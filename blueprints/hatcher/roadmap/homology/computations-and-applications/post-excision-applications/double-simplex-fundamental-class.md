---
article_id: af_0b7faad59136939d2ec0734b
source_units: [hatcher-2-1-post-excision-applications]
declaration: theorem
origin: cited
---

# The double-simplex difference generates reduced homology

Lift `doubleSimplexFundamentalCycle R n` to a named class morphism

`R ⟶ H̃_n(doubleSimplex n;R)`

and prove that this exact morphism is an isomorphism. The main artifacts are
`Hatcher.Simplex.doubleSimplexFundamentalClass` and
`Hatcher.Simplex.doubleSimplexFundamentalClass_isIso`.

Use the reduced-to-relative comparison for the pair consisting of the double
simplex and its contractible second summand, followed by the canonical
relative comparison from the first simplex. Prove at chain level that the
difference cycle maps to the identity simplex: the second summand vanishes in
the relative quotient and the first remains. The integral specialization
therefore says that `Δ₁^n - Δ₂^n`, with the common vertex ordering, is a
generator rather than merely that the group is abstractly cyclic.

## Depends on

- [The ordered difference of the two simplices is a cycle](double-simplex-fundamental-cycle.md)

## Proof depends on

- [The identity simplex generates relative simplex homology](relative-simplex-fundamental-class.md)
- [The first simplex computes homology relative to the second](double-simplex-relative-comparison.md)
- [A contractible subspace compares reduced and relative homology](contractible-subspace-relative-reduced-homology.md)
- [The pointed relative-to-reduced comparison is natural](../../simplicial-and-singular/relative-homology/good-pair-quotient/pointed-relative-reduced-homology-naturality.md)

## Sources

- [Hatcher §2.1, sphere generator in Example 2.23, printed page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
