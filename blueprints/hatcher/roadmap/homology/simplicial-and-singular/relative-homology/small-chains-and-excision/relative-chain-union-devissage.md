---
article_id: af_85e867a8cc904f3010b21537
source_units: [hatcher-2-1-small-chains-excision]
declaration: theorem
origin: bridged
---

# Relative excision reduces to the union subcomplex

Let `f : P ⟶ Q` be a morphism of simplicial-set pairs whose ambient component
is monic, and let `Z` be a subcomplex of `Q.right`. Work with
`{C : Type u}`, `[Category.{v} C]`, `[Preadditive C]`,
`[HasCoproducts.{w} C]`, and `R : C`.

The main theorem, intended as
`Hatcher.Excision.relativeChainMap_homotopyEquivalence_iff`, assumes

`Z = range(Q.hom) ⊔ range(f.right)`

and

`range(f.left ≫ Q.hom) = range(Q.hom) ⊓ range(f.right)`.

It says that the relative chain map induced by `f` is a chain-homotopy
equivalence exactly when the chain map induced by `Z.ι` is one. Specializing
to two subcomplexes `A` and `B` of a simplicial set `X` gives the canonical map

`C_*(B;R) / C_*(A ∩ B;R) → C_*(X;R) / C_*(A;R)`

and reduces its homotopy-equivalence property to that of the inclusion
`A ⊔ B → X`.

The degreewise split short complex behind this theorem is the categorical form
of Hatcher's chain isomorphism

`C_*(B;R) / C_*(A ∩ B;R) ≅ C_*^{A+B}(X;R) / C_*(A;R)`.

## Depends on

- [Relative homology of a simplicial-set pair](../simplicial-pair-relative-homology.md)

## Sources

- [Hatcher §2.1, relative quotient comparison in the excision proof, page 124](../../../../../sources/hatcher-2-1.md)
- [Singular excision implementation specification](../../../../../sources/excision-implementation.md)
- [Riou's relative dévissage implementation prior art](https://github.com/joelriou/excision/blob/8b56cd0c8e5f39a7c2f36418c80b298e469596a6/Excision/SimplicialSet/Devissage.lean)
