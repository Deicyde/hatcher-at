---
article_id: af_6ac8441d977814c7a46ab804
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Sphere.neighborhoodLocalDegree_eq_of_subset
---

# Local degree is unchanged when the neighborhood shrinks

Let `N` be a local-degree neighborhood and let `M` be a second such
neighborhood whose open set is contained in that of `N`. The inclusion of the
punctured pair of `M` into the punctured pair of `N` induces an isomorphism on
relative homology and makes the two local pair maps commute.

Name the pair-level triangle
`Hatcher.Sphere.LocalDegreeNeighborhood.restrictionPairHom_comp_pairHom` and
its induced homology equation
`Hatcher.Sphere.LocalDegreeNeighborhood.restrictionMap_comp_pairHom_map`.
Also expose a sphere-specific `IsIso` wrapper for the restriction map. The two
neighborhoods are arbitrary witnesses for the same `f`, `x`, and `y`; `M` need
not be definitionally produced by `N.restrict`.

The main theorem `Hatcher.Sphere.neighborhoodLocalDegree_eq_of_subset` states

`neighborhoodLocalDegree n hn M = neighborhoodLocalDegree n hn N`.

Prove the equality from the two oriented class equations and the naturality of
the open-neighborhood comparison, not by unfolding a choice of inverse.

The pair and homology triangles are
`Hatcher.Sphere.LocalDegreeNeighborhood.restrictionPairHom_comp_pairHom` and
`Hatcher.Sphere.LocalDegreeNeighborhood.restrictionMap_comp_pairHom_map`.
The sphere-specific isomorphism wrapper is
`Hatcher.Sphere.LocalDegreeNeighborhood.restrictionMap_isIso`, and shrinking
invariance is `Hatcher.Sphere.neighborhoodLocalDegree_eq_of_subset`.

## Depends on

- [Local degree on a chosen isolated neighborhood](neighborhood-local-degree.md)

## Sources

- [Hatcher §2.2, neighborhood identifications in local degree, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
