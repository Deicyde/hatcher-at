---
article_id: af_1f0213e0638fc4d49b7907ba
source_units: [hatcher-2-1-small-chains-excision]
declaration: theorem
origin: cited
---

# Binary-cover excision induces homology isomorphisms

**Hatcher, Theorem 2.20 (pages 119 and 124), binary-cover form.** If
`interior A ∪ interior B = Set.univ`, write
`h : Hatcher.Excision.CoverCondition A B` for this hypothesis. Then for every
degree `n` the canonical map

`H_n(B, A ∩ B;R) → H_n(X,A;R)`

induced by inclusion is an isomorphism. The intended main declaration
`Hatcher.Excision.coverHomologyMap_isIso` is an `IsIso` instance for the exact
morphism

`(Hatcher.Relative.homologyFunctor R n).map`
`  (Hatcher.Excision.coverPairHom h)`.

State the result for `{C : Type u}`, `[Category.{v} C]`, `[Preadditive C]`,
`[HasCoproducts.{w} C]`, `[CategoryWithHomology C]`, and `R : C`. Hatcher's
integral theorem is its specialization to `AddCommGrpCat.of ℤ`. Derive the
instance from the chain-level homotopy equivalence using the pinned
`HomologicalComplex.homotopyEquivalences_le_quasiIso` and
`HomotopyEquiv.toHomologyIso` machinery; do not replace the canonical map by
an unspecified isomorphism.

## Depends on

- [The binary-cover excision chain map is a homotopy equivalence](binary-cover-excision-chain-equivalence.md)
- [Relative singular chains and homology](../relative-singular-homology.md)

## Proof depends on

- [A chain map induces a map on homology](../../chain-map-homology.md)

## Sources

- [Hatcher §2.1, Theorem 2.20, pages 119 and 124](../../../../../sources/hatcher-2-1.md)
- [Singular excision implementation specification](../../../../../sources/excision-implementation.md)
