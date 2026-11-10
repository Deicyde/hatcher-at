---
article_id: af_a5ded7ecaa7b856ace06f12b
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.ClassicalCW.finiteStageHomologyStability
---

# Higher finite skeleta preserve low-degree homology

For every n ≤ m, the actual inclusion Xⁿ → Xᵐ of a classical CW complex
induces a surjection on ordinary integral Hₖ when k ≤ n and an isomorphism
when k < n. Include the identity inclusion n = m and arbitrary cell sets.

## Proof sketch

Iterate one-stage stability and identify the composites with the actual
skeletal inclusion by homology functoriality. No ambient finite-dimensional
homology conclusion is assumed.

## Depends on

- [Singular homology](../../simplicial-and-singular/singular-homology.md)

## Proof depends on

- [Skeleton step homology stability](skeleton-step-homology-stability.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)
