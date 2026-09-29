---
article_id: af_3d33a544b876beec3eeff46e
source_units: [hatcher-2-1-sphere-homology]
declaration: def
origin: bridged
---

# The zero-sphere is a two-point space

Construct the explicit universe-polymorphic isomorphism

`Hatcher.Sphere.zeroSphereIsoTwoPoint :`
`  TopCat.sphere (u := w) 0 ≅ TopCat.of (ULift.{w} Bool)`.

The two points must be distinguished explicitly and the isomorphism should
make the induced map on path components usable by the degree-zero homology
calculation. This node only identifies the topological model; it does not
compute homology.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §2.1, Propositions 2.7–2.8 and the `S⁰` base case in Corollary 2.14](../../../../sources/hatcher-2-1.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
