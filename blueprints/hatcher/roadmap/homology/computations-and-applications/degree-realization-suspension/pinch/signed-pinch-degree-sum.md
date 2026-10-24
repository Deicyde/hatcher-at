---
article_id: af_28aa787eaafee642920f2b12
source_units: [hatcher-2-2-degree-realization-suspension]
declaration: theorem
origin: bridged
---

# The degree of a signed pinch map is the sum of its signs

For n > 0, k : ℕ, and the constructed signed pinch map fσ, prove degree(fσ) = ∑ i : Fin k, σᵢ.

## Proof sketch

Choose y ≠ b and apply Proposition 2.30 to the actual finite fiber. Reindex by its equivalence with Fin k and substitute the computed local degrees. The empty-index case is the same argument with an empty sum and gives degree zero.

## Depends on

- [Reflections correct the signs of a sphere fold map](signed-sphere-fold-map.md)
- [sphere degree definition](../../degree/sphere-degree-definition.md)

## Proof depends on

- [Regular pinch fibers are indexed by the chosen balls](signed-pinch-fiber.md)
- [The signed pinch map has the prescribed local degrees](signed-pinch-local-degree.md)
- [degree local sum formula](../../local-degree/degree-local-sum-formula.md)

## Sources

- [Hatcher §2.2, printed pages 136–137](../../../../../sources/hatcher-2-2-degree-applications.md#example-231)
- [Degree-realization and suspension specification](../../../../../sources/degree-applications-implementation.md)
