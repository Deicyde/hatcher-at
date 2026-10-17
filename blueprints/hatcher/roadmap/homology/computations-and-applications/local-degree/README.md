---
article_id: af_354f1dc948b7b1d508d99160
---

# Local degree and the sum over a finite fiber

Hatcher §2.2, printed pages 135–136. This milestone orients the relative
homology at a point of a positive-dimensional sphere, defines local degree at
an isolated preimage, and proves Proposition 2.30: global degree is the sum of
the local degrees over a finite fiber.

The proof keeps Hatcher's actual maps visible. A reusable sigma-pair API gives
the direct sum of the local relative groups, disjoint open neighborhoods give
the finite-puncture excision comparison, and naturality sends the oriented
sphere class to the sum of its local classes.

Fifteen of the twenty formalization leaves below are formalized locally. Five
remain; the current ready frontier is
[relative homology of sigma pairs](relative-homology-sigma-pair.md).

## Coproduct and excision infrastructure

- [The coproduct of a family of topological pairs](sigma-topological-pair.md)
- [Relative chains commute with coproducts of arbitrary pairs](relative-chains-sigma-pair.md)
- [Relative homology commutes with coproducts of arbitrary pairs](relative-homology-sigma-pair.md)
- [A disjoint open family is homeomorphic to its sigma type](disjoint-open-union-homeomorphism.md)
- [Deleted-pair homology is local on an open neighborhood](deleted-pair-open-neighborhood.md)
- [Disjoint punctured neighborhoods form the deleted union pair](disjoint-punctured-pair-iso.md)

## Local degree

- [The ordered sphere class orients local homology](sphere-local-orientation.md)
- [An isolated preimage gives a map of punctured pairs](isolated-preimage-neighborhood.md)
- [Local degree on a chosen isolated neighborhood](neighborhood-local-degree.md)
- [Local degree is unchanged when the neighborhood shrinks](local-degree-shrinking.md)
- [Local degree is independent of its neighborhood](local-degree-well-defined.md)
- [A local homeomorphism has local degree plus or minus one](homeomorphism-local-degree.md)

## Finite fibers

- [A finite sphere-map fiber has disjoint isolated neighborhoods](finite-fiber-neighborhoods.md)
- [The disjoint local pairs excise to the finite-puncture pair](finite-puncture-pair-excision.md)
- [Finite-puncture homology is the coproduct of the local groups](finite-puncture-homology-coproduct.md)
- [Finite-puncture projections have the diagonal matrix](finite-puncture-projection-matrix.md)
- [The finite-puncture class is the sum of the local classes](finite-puncture-orientation-sum.md)
- [The finite-fiber pair map acts by the local degrees](finite-fiber-local-map.md)
- [The finite-fiber pair map carries the global degree](global-degree-fiber-square.md)
- [Degree is the sum of the local degrees](degree-local-sum-formula.md)

## Boundary

This milestone stops after Proposition 2.30. Examples 2.31–2.32, suspension
invariance in Proposition 2.33, cellular homology, the Hopf converse, and
Theorem 2.27 remain deferred.

## Sources

- [Hatcher §2.2, local degree and Proposition 2.30, printed pages 135–136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
