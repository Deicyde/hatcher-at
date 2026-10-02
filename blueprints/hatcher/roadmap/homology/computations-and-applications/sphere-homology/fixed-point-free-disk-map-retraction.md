---
article_id: af_d07b06943e65422125e14267
source_units: [hatcher-2-1-corollary-2-15]
declaration: theorem
origin: bridged
---

# A fixed-point-free disk map produces a boundary retraction

For every `n : ℕ`, let

`f : TopCat.disk.{0} (n + 1) ⟶ TopCat.disk.{0} (n + 1)`

and assume

`hf : ∀ x : TopCat.disk.{0} (n + 1), f x ≠ x`.

Then construct a morphism

`r : TopCat.disk.{0} (n + 1) ⟶ TopCat.diskBoundary.{0} (n + 1)`

with `TopCat.diskBoundaryInclusion.{0} (n + 1) ≫ r = 𝟙 _`.

The intended main result is
`Hatcher.Disc.exists_diskBoundary_retraction_of_fixedPointFree`. On the raw
closed ball, send `x` to the point where the ray from `f(x)` through `x` exits
the ball. The fixed-point-free hypothesis makes the ray nondegenerate;
continuity of its exit parameter and the boundary formula show that this map
is a retraction. Transport the construction through Mathlib's `ULift` disk
model.

## Depends on

None.

## Sources

- [Hatcher §1.1, proof of Theorem 1.9, pages 31–32](../../../../sources/hatcher-1-1.md)
- [Hatcher §2.1, Corollary 2.15, pages 114–115](../../../../sources/hatcher-2-1.md)
- [Corollary 2.15 implementation specification](../../../../sources/corollary-2-15-implementation.md)
