---
not_ready: true
---

# Poincaré duality

Hatcher §3.3 (pages 230–260). Mapped, not yet decomposed.

For a closed `R`-orientable `n`-manifold `M`, cap product with the fundamental
class `[M] ∈ Hₙ(M; R)` is an isomorphism `Hᵏ(M; R) ≅ H_{n−k}(M; R)`. The
section first has to make orientation and the fundamental class precise, which
it does through the local homology groups `Hₙ(M, M − {x})`, then proves the
duality theorem by a direct limit argument over compact sets, then connects it
to cup product and derives Alexander and Lefschetz duality.

This is the deepest result in the mapped portion of the book and the furthest
from Mathlib. It needs all of Chapter 2, all of §3.1 and §3.2, and a treatment
of manifolds compatible with Mathlib's existing `Manifold` hierarchy. It is
mapped to fix the target, not because it is close.

## Sources

- [Hatcher §3.3](../../../sources/hatcher.md)
