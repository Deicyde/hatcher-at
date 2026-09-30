---
article_id: af_aaaedd2fdc35d4e3dfcabaae
source_units: [hatcher-2-1-sphere-homology]
declaration: theorem
origin: cited
lean: Hatcher.Reduced.homologyMap_eq_of_homotopy
statement: formalized
proof: formalized
---

# Homotopic maps induce the same reduced-homology map

Let `C` have a category structure, coproducts, a preadditive structure, and
homology. For maps `f g : X ⟶ Y` in `TopCat`, a coefficient object `R : C`,
and a homotopy from `f` to `g`, prove that the two morphisms induced on reduced
homology agree in every degree:

`(Hatcher.Reduced.homologyFunctor R n).map f =`
`  (Hatcher.Reduced.homologyFunctor R n).map g`.

The main result is
`Hatcher.Reduced.homologyMap_eq_of_homotopy`. Supporting declarations should
lift augmentation-compatible chain maps and chain homotopies through
`ChainComplex.augment` in a neutral module. This avoids importing the
higher-level excision development merely to reuse its current private helper.

## Depends on

- [Reduced singular homology](../../simplicial-and-singular/relative-homology/reduced-singular-homology.md)

## Proof depends on

- [A topological homotopy gives a singular-chain homotopy](../../simplicial-and-singular/topological-homotopy-chain-homotopy.md)
- [Chain-homotopic maps induce the same homology map](../../simplicial-and-singular/chain-homotopy-invariance.md)

## Sources

- [Hatcher §2.1, reduced induced maps and homotopy invariance, pages 111–113](../../../../sources/hatcher-2-1.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
