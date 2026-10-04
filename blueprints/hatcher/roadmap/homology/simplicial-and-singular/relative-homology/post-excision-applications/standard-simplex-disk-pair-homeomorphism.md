---
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: bridged
---

# The standard simplex pair is homeomorphic to the disk pair

Construct an isomorphism of topological pairs between the ordered standard
simplex and Mathlib's standard disk:

`(Δ[n], ∂Δ[n]) ≅ (TopCat.disk n, TopCat.diskBoundary n)`.

The main artifact is `Hatcher.Simplex.standardSimplexPairIsoDiskPair`. Build
it from an explicit affine-hyperplane model followed by radial gauge
rescaling, and prove that the boundary is carried to the unit sphere. Cover
`n = 0`, where both boundaries are empty.

This is the precise equivalence used when Hatcher replaces
`(D^n, ∂D^n)` by `(Δ^n, ∂Δ^n)`. It may transport the ordered simplex
fundamental class to the disk pair, but it must not claim a canonical
Euclidean orientation unless the chosen homeomorphism proves that stronger
compatibility.

## Depends on

- [The boundary and zero horn of a standard topological simplex](standard-simplex-boundary-horn.md)

## Sources

- [Hatcher §2.1, first paragraph of Example 2.23, printed page 125](../../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../../sources/post-excision-applications-implementation.md)
