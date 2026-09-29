---
article_id: af_8bce459d247605e450eef75c
source_units: [hatcher-2-1-sphere-homology]
declaration: theorem
origin: cited
---

# Reduced homology of a contractible space vanishes

Let `C` be an abelian category with the required coproducts,
`[ContractibleSpace X]`, and `R : C`. For every `n : ℕ`, prove

`IsZero ((Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of X))`.

The main result is
`Hatcher.Reduced.isZero_homology_of_contractible`. Transport reduced homology
along a contraction equivalence with a point and use the existing reduced
point calculation.

## Depends on

- [Reduced singular homology](../../simplicial-and-singular/relative-homology/reduced-singular-homology.md)

## Proof depends on

- [A homotopy equivalence induces reduced-homology isomorphisms](homotopy-equivalence-reduced-homology-iso.md)
- [Relative homology at a basepoint is reduced homology](../../simplicial-and-singular/relative-homology/pointed-relative-reduced-homology.md)

## Sources

- [Hatcher §2.1, reduced homology of contractible spaces, page 111](../../../../sources/hatcher-2-1.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
