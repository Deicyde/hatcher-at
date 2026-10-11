---
article_id: af_79a8181ed895e3e9b2e4e24e
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: cited
---

# A local homeomorphism has local degree plus or minus one

Suppose a local-degree neighborhood `U` maps homeomorphically onto an open
neighborhood `V` of `y`. The induced map of local relative groups is an
isomorphism, so its integer multiplier is a unit.

Package this hypothesis as
`Hatcher.Sphere.LocalDegreeNeighborhood.LocalHomeomorphData N`, containing
the open target neighborhood, a homeomorphism `N.U ≃ₜ V`, and the exact
pointwise equation identifying that homeomorphism with the restriction of
`f`. Define its punctured-pair isomorphism, prove that its forward map followed
by inclusion of `V` into the target punctured sphere is exactly `N.pairHom`,
and deduce that the actual homology map induced by `N.pairHom` is an
isomorphism.

The main theorem
`Hatcher.Sphere.localDegree_eq_one_or_neg_one_of_localHomeomorph` says that
the local degree is `1` or `-1`. As a source-facing specialization, for
`e : Sⁿ ≃ₜ Sⁿ`, `x : Sⁿ`, and any isolation witness at `x` over `e x`, prove
the ordered equality
`Hatcher.Sphere.localDegree_homeomorph_eq_degree` with
`Hatcher.Sphere.degree n hn (TopCat.isoOfHomeo e).hom`.

The equality must respect the ordered orientation fixed by the completed
degree development; an unsigned statement that only proves the local map is
an isomorphism is not sufficient.

## Depends on

- [Local degree is independent of its neighborhood](local-degree-well-defined.md)
- [The formal properties of degree](../degree/basic-degree-properties.md)

## Sources

- [Hatcher §2.2, homeomorphism example for local degree, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
