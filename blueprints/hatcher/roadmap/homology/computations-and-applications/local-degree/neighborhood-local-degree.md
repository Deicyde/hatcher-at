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

The main theorem
`Hatcher.Sphere.localFundamentalClass_map_eq_neighborhoodLocalDegree` is the
class equation saying that the induced local map sends the transported source
class to the target class multiplied by `neighborhoodLocalDegree`.

## Depends on

- [The ordered sphere class orients local homology](sphere-local-orientation.md)
- [An isolated preimage gives a map of punctured pairs](isolated-preimage-neighborhood.md)

## Sources

- [Hatcher §2.2, definition of local degree, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
