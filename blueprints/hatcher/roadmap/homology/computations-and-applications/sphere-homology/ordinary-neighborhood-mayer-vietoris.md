---
article_id: af_07d3736d22868453762d05f0
source_units: [hatcher-2-2-mv-transport-sphere-recurrence]
declaration: theorem
origin: cited
---

# The ordinary neighborhood-retract Mayer–Vietoris sequence

Let `C` be an abelian category with the coproducts required by the completed
Mayer–Vietoris API, and let `R : C`. For subsets `A B : Set X`, package the
structure `Hatcher.MayerVietoris.NeighborhoodCover A B`, with neighborhoods
`U V : Set X` as fields, from the following data:
`A ∪ B = Set.univ`, `A ⊆ interior U`,
`B ⊆ interior V`, and strong deformation retractions along the subtype
inclusions from `U` to `A`, from `V` to `B`, and from `U ∩ V` to `A ∩ B`.
The neighborhood hypotheses must produce
`Hatcher.Excision.CoverCondition U V` rather than incorrectly asserting that
the interiors of `A` and `B` cover `X`.

Define the ordinary Mayer–Vietoris sequence on the homology of `A ∩ B`, `A`,
`B`, and `X`, with the signed intersection map and addition map induced by the
actual inclusions. The main result
`Hatcher.MayerVietoris.neighborhoodSequence_exact` proves every adjacent
six-term window exact; include the degree-zero epimorphism as a supporting
theorem.

Transport the open-cover sequence for `U,V` across the three homology
isomorphisms. Prove that the transported first and second maps are Hatcher's
inclusion-induced maps, not merely unspecified conjugates. The connecting map
may be defined by this transport. Since
`StrongDeformationRetract.toHomotopyEquiv` points from a neighborhood to its
retract, construct each inclusion-induced homology isomorphism from
`sdr.toHomotopyEquiv.symm`.

This node also owns moving `Hatcher.StrongDeformationRetract` and its elementary
lemmas from the Van Kampen implementation into a neutral topology module while
preserving their public names. The relocation prevents downstream homology and
sphere files from importing an unrelated high-level theorem file.

## Depends on

- [The binary-cover Mayer–Vietoris sequence](../mayer-vietoris/binary-cover-mayer-vietoris-sequence.md)
- [The standard cover of a well-pointed wedge](../../../fundamental-group/van-kampen/well-pointed-wedge-cover.md)

## Proof depends on

- [A homotopy equivalence induces homology isomorphisms](../../simplicial-and-singular/homotopy-equivalence-homology-iso.md)

## Sources

- [Hatcher §2.2, neighborhood-deformation-retract extension, page 150](../../../../sources/hatcher-2-2.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
