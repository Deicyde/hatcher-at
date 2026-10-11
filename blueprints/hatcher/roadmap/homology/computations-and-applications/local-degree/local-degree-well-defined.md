---
article_id: af_900f5d8974f03b1b5ecf96b7
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: bridged
---

# Local degree is independent of its neighborhood

The intersection of any two local-degree neighborhoods is again an open
local-degree neighborhood contained in both. Use shrinking invariance to prove
that their neighborhood local degrees agree. Expose this data as
`Hatcher.Sphere.LocalDegreeNeighborhood.inter`, its left and right subset
lemmas, and the arbitrary-neighborhood theorem
`Hatcher.Sphere.neighborhoodLocalDegree_eq`.

Define `Hatcher.Sphere.localDegree n hn f x y h` for
`h : IsolatedPreimage f x y` by choosing one witness. The main theorem
`Hatcher.Sphere.localDegree_eq_neighborhoodLocalDegree` identifies this public
integer with the value from every packaged neighborhood. Publish an explicit
proof-irrelevance theorem for two isolation witnesses and the reassociated,
choice-free local fundamental-class equation
`Hatcher.Sphere.localFundamentalClass_map_eq_localDegree`, stated against an
arbitrary packaged neighborhood.

The theorem must make local degree proof-irrelevant in the
`IsolatedPreimage` witness and independent of all open-neighborhood data. A
classical chosen witness may appear inside the definition, but no chosen
neighborhood accessor or implementation choice appears in the public theorem
signatures.

## Depends on

- [Local degree is unchanged when the neighborhood shrinks](local-degree-shrinking.md)

## Sources

- [Hatcher §2.2, definition of local degree, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
