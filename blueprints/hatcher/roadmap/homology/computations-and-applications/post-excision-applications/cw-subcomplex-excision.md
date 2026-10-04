---
article_id: af_e05bd43fe7cbd9529f3e41d0
source_units: [hatcher-2-1-post-excision-applications]
declaration: corollary
origin: cited
---

# Excision holds for a union of CW subcomplexes

**Hatcher, Corollary 2.24 (printed page 126).** Let a classical CW complex
`C` be the union of subcomplexes `A` and `B`. Define the canonical inclusion
of topological pairs

`(B, A ∩ B) ⟶ (C, A)`

and prove that it induces an isomorphism on relative singular homology in
every degree. The main artifacts are
`Hatcher.ClassicalCW.subcomplexExcisionPairHom` and
`Hatcher.ClassicalCW.subcomplexExcision_homologyMap_isIso`.

Use the compatible regular neighborhoods supplied by Appendix Proposition
A.5. Enlarge `(B,A ∩ B)` to `(N(B),N(A) ∩ N(B))`, apply binary-cover
excision to `(N(B),N(A) ∩ N(B)) → (C,N(A))`, and compare `(C,A)` with
`(C,N(A))` through the strong deformation retraction. Identify the resulting
composite with the displayed canonical pair map.

This route includes `A ∩ B = ∅`. Do not use only Proposition 2.22 for the
final theorem, since the project's good-pair structure deliberately requires
a nonempty subspace.

## Depends on

- [Relative singular chains and homology](../../simplicial-and-singular/relative-homology/relative-singular-homology.md)

## Proof depends on

- [Subcomplex decompositions admit compatible neighborhoods](cw-subcomplex-neighborhood/subcomplex-neighborhood-cover.md)
- [Binary-cover excision induces an isomorphism on relative homology](../../simplicial-and-singular/relative-homology/small-chains-and-excision/binary-cover-excision-homology-isomorphism.md)
- [Relative-homology isomorphism from component isomorphisms](../../simplicial-and-singular/relative-homology/good-pair-quotient/relative-homology-map-isomorphism-criterion.md)
- [A homotopy equivalence induces homology isomorphisms](../../simplicial-and-singular/homotopy-equivalence-homology-iso.md)

## Sources

- [Hatcher §2.1, Corollary 2.24, printed page 126](../../../../sources/hatcher-2-1.md)
- [Hatcher, Appendix Proposition A.5, printed page 523](../../../../sources/hatcher-appendix-a5.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
- [CW-subcomplex neighborhood implementation specification](../../../../sources/cw-subcomplex-neighborhood-implementation.md)
