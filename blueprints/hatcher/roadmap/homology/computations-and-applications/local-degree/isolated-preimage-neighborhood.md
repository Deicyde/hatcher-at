---
article_id: af_70b8f0060e881e7493096139
source_units: [hatcher-2-2-local-degree]
declaration: structure
origin: bridged
---

# An isolated preimage gives a map of punctured pairs

For a sphere map `f` and points `x` and `y`, define
`Hatcher.Sphere.LocalDegreeNeighborhood f x y` to package an open set `U`,
membership `x ∈ U`, the equality `f x = y`, and the assertion that a point of
`U` mapping to `y` equals `x`. Define
`Hatcher.Sphere.IsolatedPreimage f x y` as the nonemptiness of this structure.

The main artifact is `Hatcher.Sphere.LocalDegreeNeighborhood.pairHom`, the
canonical morphism

`(U, U \ {x}) ⟶ (Sⁿ, Sⁿ \ {y})`

induced by the restriction of `f`. Prove its ambient and punctured-subspace
component formulas without exposing subtype proof terms. Provide
`Hatcher.Sphere.LocalDegreeNeighborhood.restrict` for a smaller open set
containing `x`, and show that every packaged neighborhood supplies an
`IsolatedPreimage` witness. The generic morphism between nested punctured
neighborhood pairs belongs to the local-orientation node and is not duplicated
here.

## Depends on

- [Local homology is unchanged on an open neighborhood](../local-homology-and-dimension/local-homology-open-neighborhood.md)

## Sources

- [Hatcher §2.2, neighborhoods in the definition of local degree, printed pages 135–136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
