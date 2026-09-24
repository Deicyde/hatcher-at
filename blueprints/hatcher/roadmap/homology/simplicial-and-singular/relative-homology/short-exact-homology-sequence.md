---
article_id: af_22af3ad0a34dfc2e051ccf6b
source_units: [hatcher-2-1-relative-homology-les]
declaration: theorem
origin: cited
mathlib: true
mathlib_declaration: HomologicalComplex.HomologySequence.composableArrows₅_exact
mathlib_file: Mathlib/Algebra/Homology/HomologySequenceLemmas.lean
---

# A short exact sequence gives an exact homology sequence

**Hatcher, Theorem 2.16 (pages 116–117).** A short exact sequence of chain
complexes in an abelian category induces an exact long sequence in homology,
with connecting maps lowering degree by one.

The pinned theorem
`HomologicalComplex.HomologySequence.composableArrows₅_exact` proves the
exactness of every consecutive six-object segment. Together with its
degree parameters, these segments are Hatcher's long exact sequence. The
connecting morphism and the three local exactness statements are supplied by
`CategoryTheory.ShortComplex.ShortExact.δ` and
`homology_exact₁/₂/₃` in the same API.

For a complex indexed by `ℕ`, the six-object theorem does not itself express
the terminal epimorphism into degree-zero homology. The pinned supporting
lemma `HomologicalComplex.epi_homologyMap_of_epi_of_not_rel` supplies that
endpoint when there is no lower degree; the pair-specific API exposes the
corresponding `Epi` instance for its degree-zero relative-chain projection.

## Depends on

- [A chain map induces a map on homology](../chain-map-homology.md)

## Sources

- [Hatcher §2.1, Theorem 2.16, pages 116–117](../../../../sources/hatcher-2-1.md)
