---
article_id: af_7e40bcc1610ef4c11f35a6bb
source_units: [hatcher-2-1-good-pair-quotient]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Relative.pointQuotientComparison_homologyMap_isIso_of_isGoodPair
---

# Good-pair relative homology is reduced quotient homology

**Hatcher, Proposition 2.22 (printed page 124).** For every good pair and every
degree, prove that the exact canonical map induced by
`Hatcher.Relative.pointQuotientComparison` is an isomorphism

`H_n(X,A;R) → H_n(X/A,A/A;R)`.

Compose it with `Hatcher.Relative.pointedPairHomologyIso` to define

`Hatcher.Relative.goodPairRelativeHomologyIsoReducedPointQuotient :`
`  H_n(X,A;R) ≅ H̃_n(X/A;R)`.

Its forward map must be definitionally or propositionally identified with the
quotient-induced relative map followed by the pointed comparison.

Applying relative homology to the canonical neighborhood square identifies
the desired quotient map followed by the quotient-neighborhood comparison
with the composite of the original-neighborhood and neighborhood-quotient
comparisons. The three latter maps are isomorphisms, so categorical
cancellation proves that the exact map induced by
`pointQuotientComparison.app P` is an isomorphism in every degree, including
degree zero. The proof is first given for `GoodPairData` and then descends
through `IsGoodPair`, without requiring maps of pairs to preserve a chosen
neighborhood witness.

The definition
`Hatcher.Relative.goodPairRelativeHomologyIsoReducedPointQuotient` composes
this exact quotient-induced isomorphism with `pointedPairHomologyIso`. Its
companion `_hom` theorem identifies the forward map exactly with the required
quotient-induced relative map followed by the pointed comparison.

## Depends on

- [Good pairs and neighborhood deformation retracts](good-pair-data.md)
- [Functorial point quotients of topological pairs](point-quotient-functor.md)
- [Relative homology at a basepoint is reduced homology](../pointed-relative-reduced-homology.md)

## Proof depends on

- [The complementary excision diagram](good-pair-excision-diagram.md)
- [Enlarging to the chosen neighborhood preserves relative homology](good-pair-neighborhood-relative-homology.md)
- [Enlarging the quotient point preserves relative homology](point-quotient-neighborhood-relative-homology.md)
- [The neighborhood quotient map preserves relative homology](point-quotient-neighborhood-excision.md)

## Sources

- [Hatcher §2.1, Proposition 2.22, page 124](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
