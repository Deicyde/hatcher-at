---
article_id: af_5207ed172ee75a4870d0f7f2
source_units: [hatcher-2-1-sphere-homology]
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Reduced.homologyIsoOfHomotopyEquiv
---

# A homotopy equivalence induces reduced-homology isomorphisms

Let `C` have a category structure, coproducts, a preadditive structure, and
homology. For a homotopy equivalence `e : X ≃ₕ Y`, a coefficient object
`R : C`, and a degree `n`, construct an isomorphism

`H̃_n(X;R) ≅ H̃_n(Y;R)`.

Its forward morphism must be the
map induced by `e.toFun`, with a public simplification lemma parallel to the
ordinary singular-homology API. Construct the inverse from `e.invFun` and use
reduced homotopy invariance for the inverse laws.

## Depends on

- [Reduced singular homology](../../simplicial-and-singular/relative-homology/reduced-singular-homology.md)

## Proof depends on

- [Homotopic maps induce the same reduced-homology map](reduced-homology-homotopy-invariance.md)

## Sources

- [Hatcher §2.1, Corollary 2.11 and the reduced analogue, pages 111–113](../../../../sources/hatcher-2-1.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
