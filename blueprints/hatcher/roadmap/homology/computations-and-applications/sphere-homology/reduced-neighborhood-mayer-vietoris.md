---
article_id: af_66ea1f639ef9bbd0f6236d16
source_units: [hatcher-2-2-mv-transport-sphere-recurrence]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.MayerVietoris.reducedNeighborhoodLongExact
---

# The reduced neighborhood-retract Mayer–Vietoris sequence

Let `C` be an abelian category with the coproducts required by the completed
Mayer–Vietoris API, and let `R : C`. For
`Hatcher.MayerVietoris.NeighborhoodCover A B`, define the reduced sequence on
`H̃_*(A ∩ B;R)`, `H̃_*(A;R)`, `H̃_*(B;R)`, and `H̃_*(X;R)`. Its intersection
and union maps are induced by the actual subspace inclusions with the same
signs as the binary-cover sequence.

The main theorem `Hatcher.MayerVietoris.reducedNeighborhoodLongExact`
packages exactness of every adjacent-degree window and, when `A ∩ B` is
nonempty, the terminal exact sequence ending in `H̃_0(X;R) ⟶ 0`. Supporting
naturality lemmas must identify the transported maps with the public reduced
intersection and union maps. This node owns public formulas expressing the
existing `reducedIntersectionMap` as the signed biproduct lift and
`reducedUnionMap` as `biprod.desc` of the two inclusion-induced maps; the
current private augmented-chain definitions are not an adequate downstream
API by themselves.

## Depends on

- [The ordinary neighborhood-retract Mayer–Vietoris sequence](ordinary-neighborhood-mayer-vietoris.md)
- [The reduced binary-cover Mayer–Vietoris sequence](../mayer-vietoris/reduced-binary-cover-mayer-vietoris-sequence.md)

## Proof depends on

- [A homotopy equivalence induces reduced-homology isomorphisms](homotopy-equivalence-reduced-homology-iso.md)

## Sources

- [Hatcher §2.2, neighborhood-deformation-retract extension, page 150](../../../../sources/hatcher-2-2.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
