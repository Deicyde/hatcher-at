---
article_id: af_d17a273f91f8b9c2dc6da6d6
declaration: def
origin: cited
---

# Cellular homology agrees with singular homology

**Hatcher, Theorem 2.35.** For every classical CW complex X and n ∈ ℕ,
construct an isomorphism Hₙ(Ccell(X)) ≅ Hₙ(X;ℤ). Bind its forward map to the
actual relative projection jₙ and skeleton inclusion: the identification
Hₙ(Xⁿ) ≅ cyclesₙ(Ccell(X)) induced by jₙ, followed by the cellular homology
quotient and this isomorphism, equals the inclusion-induced map to Hₙ(X).
The identification and equation are proved internally. Include n = 0,
empty complexes, infinite cell families and unbounded dimensions.

## Proof sketch

Skeleton vanishing makes jₙ injective. Pair exactness identifies its image
with cellular cycles and the next connecting image with cellular boundaries.
Pass through the resulting quotients and identify the target using the
actual higher-skeleton inclusion. At n = 0 the old skeleton is empty and j₀
is an isomorphism; use ordinary, unaugmented degree-zero homology.

## Depends on

- [Cellular chain complex](cellular-chain-complex.md)
- [Singular homology](../../simplicial-and-singular/singular-homology.md)

## Proof depends on

- [Skeleton homology vanishing](skeleton-homology-vanishing.md)
- [Skeleton to space homology stability](skeleton-to-space-homology-stability.md)
- [Pair long exact sequence](../../simplicial-and-singular/relative-homology/pair-long-exact-sequence.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#theorem-235)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)
