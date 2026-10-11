---
article_id: af_fa4a1039c6e4767afd3acb10
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: cited
---

# The finite-fiber pair map acts by the local degrees

Use the canonical pair morphism

`(Sⁿ, Sⁿ - fiber f y) ⟶ (Sⁿ, Sⁿ - {y})`

defined with the finite-fiber data. For each fiber point, its composite with the inclusion of the
chosen local punctured pair is the pair map used to define local degree.

Work parametrically with arbitrary `D : FiniteFiberNeighborhoods f y` rather
than hardwiring the noncomputable constructor. Name the exact pair triangle
`Hatcher.Sphere.finitePuncturePairHomComponent_comp_finiteFiberPairMap`, using
the direct inclusion `finitePunctureNeighborhoodPairHom D i`. The canonical
isolation witness on the right is `(D.neighborhood i).isolatedPreimage`.

The main theorem `Hatcher.Sphere.finiteFiberPairMap_localClass` states that
the full local-to-finite-to-target homology composite sends the transported
oriented class of the `i`th local summand to

`AddCommGrpCat.asHom (localDegree n hn f x y hx) ≫`
`  integralSphereLocalFundamentalClass n hn y`.

The local integer must be the neighborhood-independent public local degree,
using `localDegree_eq_neighborhoodLocalDegree` for the neighborhoods supplied
by `D`. Mark both the pair triangle and class equation for reassociation. The
proof must rewrite the actual pair composite; no new isomorphism or scalar
cancellation is needed.

## Depends on

- [Local degree is independent of its neighborhood](local-degree-well-defined.md)
- [The disjoint local pairs excise to the finite-puncture pair](finite-puncture-pair-excision.md)

## Sources

- [Hatcher §2.2, upper square in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
