---
article_id: af_9896b1645c08fe4c85a03257
source_units: [hatcher-2-1-good-pair-quotient]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Relative.goodPairPointQuotientRelativeHomologyNatIso
---

# The good-pair quotient comparison is natural

Restrict relative homology and reduced homology of the point quotient to the
full subcategory of good pairs. Package the Proposition 2.22 comparisons as a
natural isomorphism
`Hatcher.Relative.goodPairPointQuotientRelativeHomologyNatIso`.

Maps of good pairs are ordinary pair morphisms and need not preserve chosen
neighborhood witnesses. Prove the canonical identity saying that reduced-pair
projection followed by the comparison is exactly the map on reduced homology
induced by the ambient quotient `q : X → X/A`.

Formalized in `Hatcher/Singular/GoodPairPointQuotientNaturality.lean`.
Relative homology and reduced homology of the functorial point quotient are
restricted to the full subcategory `Hatcher.Relative.GoodPair`. The component
at a good pair is exactly
`goodPairRelativeHomologyIsoReducedPointQuotient`; naturality follows by
combining `pointQuotientComparison.naturality` with
`pointedPairHomologyIso_naturality`. Since morphisms of the full subcategory
carry only an underlying pair map, no chosen neighborhood or deformation
retraction is preserved.

The theorem
`reducedPairProjection_comp_goodPairPointQuotientRelativeHomologyNatIso_hom_app`
also identifies the displayed composite with
`Hatcher.Reduced.homologyFunctor.map (pointQuotientProjection P.obj)` in every
degree, including degree zero.

## Depends on

- [Good pairs and neighborhood deformation retracts](good-pair-data.md)
- [Functorial point quotients of topological pairs](point-quotient-functor.md)
- [Good-pair relative homology is reduced quotient homology](good-pair-point-quotient-relative-homology.md)
- [The pointed relative-to-reduced comparison is natural](pointed-relative-reduced-homology-naturality.md)

## Sources

- [Hatcher §2.1, naturality of Theorem 2.13, page 128](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
