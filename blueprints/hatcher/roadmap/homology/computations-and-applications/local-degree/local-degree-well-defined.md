---
article_id: af_900f5d8974f03b1b5ecf96b7
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: bridged
---

# Local degree is independent of its neighborhood

The intersection of any two local-degree neighborhoods is again an open
local-degree neighborhood contained in both. Use shrinking invariance to prove
that their neighborhood local degrees agree.

Define `Hatcher.Sphere.localDegree n hn f x y h` for
`h : IsolatedPreimage f x y` by choosing one witness. The main theorem
`Hatcher.Sphere.localDegree_eq_neighborhoodLocalDegree` identifies this public
integer with the value from every packaged neighborhood. Also publish the
choice-free local fundamental-class equation.

The theorem must make local degree proof-irrelevant in the
`IsolatedPreimage` witness and independent of all open-neighborhood data.

## Depends on

- [Local degree is unchanged when the neighborhood shrinks](local-degree-shrinking.md)

## Sources

- [Hatcher §2.2, definition of local degree, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
