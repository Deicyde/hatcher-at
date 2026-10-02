---
article_id: af_a6eb442378369693c34b1c50
source_units: [hatcher-2-1-corollary-2-15]
declaration: theorem
origin: cited
---

# The boundary sphere is not a retract of the disk

For every `n : ℕ`, there is no morphism

`r : TopCat.disk.{0} (n + 1) ⟶ TopCat.diskBoundary.{0} (n + 1)`

such that

`TopCat.diskBoundaryInclusion.{0} (n + 1) ≫ r = 𝟙 _`.

The intended main result is
`Hatcher.Disc.not_exists_diskBoundary_retraction`. Apply reduced integral
homology in degree `n`. The boundary is `TopCat.sphere.{0} n`, with reduced
homology isomorphic to `ℤ`, while the contractible disk has zero reduced
homology. A retraction would make the identity of the former factor through
the latter.

## Depends on

None.

## Proof depends on

- [Reduced homology of a contractible space vanishes](contractible-space-reduced-homology.md)
- [Reduced homology of spheres](sphere-reduced-homology.md)

## Sources

- [Hatcher §2.1, Corollary 2.15, pages 114–115](../../../../sources/hatcher-2-1.md)
- [Corollary 2.15 implementation specification](../../../../sources/corollary-2-15-implementation.md)
