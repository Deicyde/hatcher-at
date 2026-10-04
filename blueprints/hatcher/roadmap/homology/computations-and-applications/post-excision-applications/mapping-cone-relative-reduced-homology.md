---
article_id: af_a2e49a25cd3a4caa14d957af
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: cited
---

# Relative homology is reduced homology of the mapping cone

**Hatcher, §2.1 (page 125).** For every topological pair `P`, coefficient
object `R` in an abelian category with the coproducts required by singular
chains, and degree `n : ℕ`, construct the isomorphism

`Hatcher.Relative.mappingConeHomologyIso P R n :`
`  (Hatcher.Relative.homologyFunctor R n).obj P ≅`
`    (Hatcher.Reduced.homologyFunctor R n).obj`
`      (Hatcher.Relative.mappingCone P)`.

This includes degree zero and imposes no good-pair, closedness, or nonemptiness
hypothesis. Hatcher's integral statement is the specialization to
`AddCommGrpCat.of ℤ`.

Let `D := mappingConeCoverPair P`, `Q := mappingConeUpperPair P`,
`F := Hatcher.Relative.homologyFunctor R n`,
`r := mappingConeCoverRetraction P`, and `e := mappingConeExcision P`. Let
`κ := contractibleSubspaceHomologyIso Q R n`, oriented from reduced ambient
homology to relative homology. Define the main isomorphism by the exact
composition

`(asIso (F.map r)).symm ≪≫ asIso (F.map e) ≪≫ κ.symm`.

Expose a simplification lemma for its inverse identifying it with

`Hatcher.Relative.reducedPairProjection Q R n ≫`
`  inv (F.map e) ≫ F.map r`.

Thus the source-order direction is precisely Hatcher's sequence: reduced
homology of the mapping cone maps to relative homology against the
contractible cone-side member; excision removes the apex-side neighborhood;
and the punctured pair retracts to `(X,A)`. Do not replace any of these
canonical morphisms by an unspecified isomorphism, and do not add functoriality
or naturality beyond the printed-page-125 claim.

## Depends on

- [The mapping cone of a topological pair](mapping-cone-model.md)
- [A contractible subspace identifies reduced and relative homology](contractible-subspace-relative-reduced-homology.md)
- [The mapping-cone cover has the relative homology of the original pair](mapping-cone-cover-relative-homology.md)
- [Relative singular chains and homology](../../simplicial-and-singular/relative-homology/relative-singular-homology.md)
- [Reduced singular homology](../../simplicial-and-singular/relative-homology/reduced-singular-homology.md)

## Proof depends on

- [Binary-cover excision induces homology isomorphisms](../../simplicial-and-singular/relative-homology/small-chains-and-excision/binary-cover-excision-homology-isomorphism.md)
- [The cone-side cover member is contractible](../../../fundamental-group/van-kampen/cell-attachment-support/single-cone-upper-contractible.md)

## Sources

- [Hatcher §2.1, arbitrary-pair mapping-cone comparison, page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
