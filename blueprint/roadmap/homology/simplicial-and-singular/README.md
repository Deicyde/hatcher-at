# Simplicial and singular homology

Hatcher §2.1 (pages 102–133). The selected first slice covers singular
homology, its low-degree checks, functoriality, and homotopy invariance through
Corollary 2.11 and Proposition 2.12.

Simplicial homology takes a Δ-complex structure and forms the chain complex of
its simplices; it is finite and computable but depends on the chosen structure.
Singular homology takes all continuous maps `Δⁿ → X` as generators; it is
manifestly functorial but visibly enormous. The section
proves homotopy invariance of singular homology by a prism decomposition,
builds the long exact sequence of a pair, proves excision by barycentric
subdivision, and concludes that the two theories agree on Δ-complexes.

The pinned Mathlib has exact categorical versions of most of this first slice.
The roadmap makes those upstream results explicit, and the two thin
source-facing consequences are formalized locally in
`Hatcher/Singular/Homology.lean`.

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

## Deferred within §2.1

Lemma 2.1 and Examples 2.2–2.5 need a source-faithful Δ-complex chain model.
Proposition 2.6 needs additivity over all path components in every degree; the
pin contains only its degree-zero case. Reduced and relative homology,
Theorems 2.13 and 2.16, excision, sphere calculations, invariance of dimension,
and the Δ-complex comparison are also deferred.

Relative homology for simplicial-set pairs merged after the repository's
Mathlib pin in PR
[#41285](https://github.com/leanprover-community/mathlib4/pull/41285).
Excision remains active upstream work. The next pass should evaluate a pin
update and follow that design rather than introduce a competing local API.

## Sources

- [Hatcher §2.1](../../../sources/hatcher-2-1.md)
