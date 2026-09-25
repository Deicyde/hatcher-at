---
article_id: af_d8263fa293c57dc52465f995
---

# Simplicial and singular homology

Hatcher §2.1 (pages 102–133). The completed first slice covers singular
homology, its low-degree checks, functoriality, and homotopy invariance through
Corollary 2.11 and Proposition 2.12. A second selected slice decomposes reduced
and relative homology, exact sequences, naturality, and relative homotopy
invariance; thirteen of its fifteen leaves are complete.

Simplicial homology takes a Δ-complex structure and forms the chain complex of
its simplices; it is finite and computable but depends on the chosen structure.
Singular homology takes all continuous maps `Δⁿ → X` as generators; it is
manifestly functorial but visibly enormous. The section
proves homotopy invariance of singular homology by a prism decomposition,
builds the long exact sequence of a pair, proves excision by barycentric
subdivision, and concludes that the two theories agree on Δ-complexes.

The pinned Mathlib has exact categorical versions of most of the first slice.
The roadmap makes those upstream results explicit, and the two thin
source-facing consequences are formalized locally in
`Hatcher/Singular/Homology.lean`. It also contains the generic algebraic long
exact sequence and, at the current `v4.34.1` pin, the `SSetPair` relative-
homology foundation from PR #41285. The four reduced-homology leaves, generic
algebraic exact-sequence leaf, simplicial-pair foundation, singular-pair
functor, relative-homology functor, pair long exact sequence, and pair-sequence
naturality are complete. The pair sequence includes the integral connecting-map
formula, and the relative homotopy branch through Proposition 2.19 and the
reduced pair sequence are complete. Two downstream leaves remain incomplete:
the pointed comparison and reduced-pair-sequence naturality, both ready to
state.

## Singular chains and low degrees

- [The singular chain complex](singular-chain-complex.md)
- [Singular homology](singular-homology.md)
- [Zeroth homology is free on path components](zeroth-homology-components.md)
- [Higher homology vanishes for totally disconnected spaces](totally-disconnected-higher-homology.md)
- [Homology of a point](point-homology.md)

## Functoriality and homotopy invariance

- [A chain map induces a map on homology](chain-map-homology.md)
- [Chain-homotopic maps induce the same homology map](chain-homotopy-invariance.md)
- [A topological homotopy gives a singular-chain homotopy](topological-homotopy-chain-homotopy.md)
- [Homotopic maps induce the same singular-homology map](singular-homology-homotopy-invariance.md)
- [A homotopy equivalence induces homology isomorphisms](homotopy-equivalence-homology-iso.md)

## Reduced and relative homology

- [Relative homology and exact sequences](relative-homology/README.md)

## Deferred within §2.1

Lemma 2.1 and Examples 2.2–2.5 need a source-faithful Δ-complex chain model.
Proposition 2.6 needs additivity over all path components in every degree;
Mathlib `v4.34.1` contains only its degree-zero case. Theorem 2.13, Example
2.17, the triple sequence, excision and quotient-pair comparison, the remaining
sphere applications, invariance of dimension, and the Δ-complex comparison
also remain deferred.

Relative homology for simplicial-set pairs merged in Mathlib PR
[#41285](https://github.com/leanprover-community/mathlib4/pull/41285) and is
present at the repository's `v4.34.1` pin. The simplicial-pair foundation is
therefore complete, and
[the singular-pair functor](relative-homology/singular-pair-functor.md) and
[relative singular homology](relative-homology/relative-singular-homology.md)
are now formalized. The
[pair long exact sequence](relative-homology/pair-long-exact-sequence.md),
including its connecting-map formula, is also formalized. Pair-sequence
naturality is now formalized. The compatible relative chain homotopy and its
induced homology-map equality complete the relative homotopy branch and
Proposition 2.19. The reduced pair sequence is now formalized. The pointed
comparison and reduced-pair-sequence naturality are ready to state. Excision
remains active upstream work.

## Sources

- [Hatcher §2.1](../../../sources/hatcher-2-1.md)
