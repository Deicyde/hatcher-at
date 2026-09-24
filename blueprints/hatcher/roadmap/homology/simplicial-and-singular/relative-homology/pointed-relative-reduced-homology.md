---
article_id: af_0d5b949221c2653c9284c81a
source_units: [hatcher-2-1-relative-homology-les]
declaration: def
origin: cited
---

# Relative homology at a basepoint is reduced homology

**Hatcher, Example 2.18 (page 118).** For a space `X` with chosen point `x₀`,
construct an isomorphism
`Hₙ(X,{x₀};R) ≅ H̃ₙ(X;R)` for every degree `n`.

The main artifact should be `Hatcher.Relative.pointedPairHomologyIso`. The
proof uses the reduced long exact sequence and the vanishing of reduced
homology of a point. It must include degree zero rather than proving only the
positive-degree case.

## Depends on

- [Relative singular chains and homology](relative-singular-homology.md)
- [Reduced singular homology](reduced-singular-homology.md)

## Proof depends on

- [The reduced long exact sequence of a nonempty pair](reduced-pair-long-exact-sequence.md)
- [Homology of a point](../point-homology.md)

## Sources

- [Hatcher §2.1, Example 2.18, page 118](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
