---
article_id: af_86dafc67e2c6c67093b0e86f
declaration: theorem
origin: bridged
---

# One skeleton attachment changes homology only in adjacent degrees

Write Sₚ = Xᵖ⁻¹ with S₀ empty. For the actual inclusion Sₚ → Sₚ₊₁,
the induced ordinary integral Hₖ map is surjective when k ≠ p and injective
when k + 1 ≠ p. It is an isomorphism when both conditions hold. Include
p = 0 and homology degree zero.

## Proof sketch

Apply the actual pair long exact sequence. The two adjacent relative terms
vanish outside the cell dimension by the skeletal relative calculation;
the degree-zero terminal window supplies the same surjectivity statement.

## Depends on

- [Singular homology](../../simplicial-and-singular/singular-homology.md)

## Proof depends on

- [Skeleton relative homology](skeleton-relative-homology.md)
- [Pair long exact sequence](../../simplicial-and-singular/relative-homology/pair-long-exact-sequence.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)
