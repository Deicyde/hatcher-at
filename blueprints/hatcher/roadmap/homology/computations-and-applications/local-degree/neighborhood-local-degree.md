---
article_id: af_3d24367a7abad40e88f4616d
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: cited
---

# Local degree on a chosen isolated neighborhood

For `0 < n` and a `LocalDegreeNeighborhood N` of `x` over `y`, transport the
ordered source local class supplied by the local-orientation node through the
homology map induced by `N.pairHom`. Conjugate by the ordered target local
orientation and evaluate at `1` to define
`Hatcher.Sphere.neighborhoodLocalDegree n hn N : ℤ`.

First define the conjugated endomorphism
`Hatcher.Sphere.neighborhoodLocalDegreeEndomorphism n hn N : ℤ ⟶ ℤ` and prove
that it is `AddCommGrpCat.asHom` of the local degree. The composition order is
source neighborhood class, induced pair map, then the target local-homology
orientation isomorphism. Do not assume that the induced pair map is an
isomorphism.

The main theorem
`Hatcher.Sphere.localFundamentalClass_map_eq_neighborhoodLocalDegree` is the
class equation saying that the induced local map sends the transported source
class to the target class multiplied by `neighborhoodLocalDegree`:

`localClass(N) ≫ H_n(N.pairHom) =`
`  AddCommGrpCat.asHom (neighborhoodLocalDegree n hn N) ≫ localClass(y)`.

Mark this equation for reassociation so later finite-fiber compositions use
the exact induced map without unfolding the conjugated endomorphism.

## Depends on

- [The ordered sphere class orients local homology](sphere-local-orientation.md)
- [An isolated preimage gives a map of punctured pairs](isolated-preimage-neighborhood.md)

## Sources

- [Hatcher §2.2, definition of local degree, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
