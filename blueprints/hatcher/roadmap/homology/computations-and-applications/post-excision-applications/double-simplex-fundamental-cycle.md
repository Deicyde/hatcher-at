---
article_id: af_570a45f4a12c99b18f2f5d42
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: cited
---

# The ordered difference of the two simplices is a cycle

Define the double-simplex space `Hatcher.Simplex.doubleSimplex n` as the
`TopCat` pushout of two copies of `Δ[n]` along their boundaries, using the
same ordering of boundary vertices on both copies. Let `σ₁` and `σ₂` be the
two singular `n`-simplices induced by the pushout inclusions.

Define

`Hatcher.Simplex.doubleSimplexFundamentalCycle R n`

to be the augmented singular chain `σ₁ - σ₂`. Prove it is a cycle: each face
of `σ₁` equals the corresponding face of `σ₂` by the pushout relation, so the
boundaries cancel term by term. The construction includes `n = 0`, where the
augmentation of the difference is zero.

This node records the exact cycle from Hatcher's Example 2.23. It does not yet
prove that the resulting reduced-homology class is a generator.

## Depends on

- [The boundary and zero horn of a standard topological simplex](standard-simplex-boundary-horn.md)
- [Reduced singular homology](../../simplicial-and-singular/relative-homology/reduced-singular-homology.md)

## Sources

- [Hatcher §2.1, second half of Example 2.23, printed page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
