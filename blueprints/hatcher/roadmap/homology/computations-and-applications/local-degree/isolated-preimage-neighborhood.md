---
article_id: af_70b8f0060e881e7493096139
source_units: [hatcher-2-2-local-degree]
declaration: structure
origin: bridged
---

# An isolated preimage gives a map of punctured pairs

For a sphere map `f`, points `x` and `y`, and `f x = y`, define
`Hatcher.Sphere.IsolatedPreimage f x y` to assert that some open neighborhood
of `x` contains no other point mapping to `y`. Define
`Hatcher.Sphere.LocalDegreeNeighborhood f x y` to package one such open set.

The main artifact is `Hatcher.Sphere.LocalDegreeNeighborhood.pairHom`, the
canonical morphism

`(U, U \ {x}) ⟶ (Sⁿ, Sⁿ \ {y})`

induced by the restriction of `f`. Prove its ambient and punctured-subspace
component formulas, provide restriction to a smaller open neighborhood, and
show that every packaged neighborhood supplies an `IsolatedPreimage` witness.

## Depends on

- [Local homology is unchanged on an open neighborhood](../local-homology-and-dimension/local-homology-open-neighborhood.md)

## Sources

- [Hatcher §2.2, neighborhoods in the definition of local degree, printed pages 135–136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
