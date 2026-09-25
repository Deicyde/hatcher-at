# Hatcher §2.1, Simplicial and Singular Homology

Numbered results in [Hatcher](hatcher.md) §2.1, pages 102–133. Printed page
numbers are used below; the PDF page is the printed page plus nine.

Statements are paraphrased. Read the actual text in the official PDF.

## Simplicial and singular chains (102–110)

Hatcher first defines the simplicial chain groups of a Δ-complex, with the
alternating sum of faces as boundary. He then defines a chain complex and its
homology, computes several small Δ-complexes, and defines singular chains by
taking all singular simplices as generators.

| Result | Page | Paraphrase |
| --- | --- | --- |
| **Lemma 2.1** | 105–106 | Consecutive simplicial boundary maps compose to zero. |
| Examples 2.2–2.4 | 106–107 | Compute simplicial homology for standard Δ-complex models of the circle, torus, and projective plane. |
| Example 2.5 | 107 | For the sphere built from two `n`-simplices, their difference generates top-degree simplicial homology; the other degrees are left for later tools. |
| **Proposition 2.6** | 109 | Singular homology in every degree splits as the direct sum over path components. |
| **Proposition 2.7** | 109–110 | A nonempty path-connected space has `H₀ ≅ ℤ`; in general `H₀` is free abelian on path components. |
| **Proposition 2.8** | 110 | A point has `H₀ ≅ ℤ` and zero homology in positive degrees. |

The reduced groups immediately following Proposition 2.8 are defined from the
augmented singular chain complex. They are part of the selected second slice;
their roadmap representation is local because Mathlib `v4.34.1` has no
packaged reduced singular homology.

## Functoriality and homotopy invariance (110–113)

A continuous map acts on singular simplices by postcomposition and therefore
gives a chain map. Hatcher proves homotopy invariance with an explicit prism
operator, then abstracts the final algebraic step to arbitrary chain
homotopies.

| Result | Page | Paraphrase |
| --- | --- | --- |
| **Proposition 2.9** | 111 | A chain map induces maps on homology. |
| **Theorem 2.10** | 111–113 | Homotopic maps induce equal maps on singular homology. |
| **Corollary 2.11** | 111 | A homotopy equivalence induces homology isomorphisms in every degree. |
| **Proposition 2.12** | 113 | Chain-homotopic chain maps induce equal maps on homology. |

## Exact sequences, excision, and comparison (113–133)

The rest of the section defines relative homology, obtains long exact
sequences from short exact sequences of chain complexes, proves excision by
subdivision into small chains, computes sphere homology, proves invariance of
dimension, and compares Δ-complex homology with singular homology.

| Result | Page | Paraphrase |
| --- | --- | --- |
| **Theorem 2.13** | 114, proved after 2.22 | A good pair gives the reduced exact sequence for `A → X → X/A`. |
| **Corollary 2.14** | 114 | Compute the reduced homology of spheres. |
| **Corollary 2.15** | 114–115 | The boundary sphere does not retract from a disk; Brouwer's fixed-point theorem follows. |
| **Theorem 2.16** | 117 | A short exact sequence of chain complexes gives a long exact sequence in homology. |
| Examples 2.17–2.18 | 117–118 | Compute disk-pair homology and identify `Hₙ(X,x₀)` with reduced homology. |
| **Proposition 2.19** | 118 | Homotopic maps of pairs induce equal maps on relative homology. |
| **Theorem 2.20** | 119–124 | Excision holds when the closure of the excised set lies in the interior of the subspace. |
| **Proposition 2.21** | 119–124 | If the interiors of a family of subsets cover `X`, chains subordinate to that family include by a chain-homotopy equivalence. |
| **Proposition 2.22** | 124–125 | For a good pair, quotienting the pair compares relative homology with reduced homology of the quotient. |
| Example 2.23 and Corollaries 2.24–2.25 | 125–126 | Apply excision and exact sequences to spheres, unions of subcomplexes, and wedge sums. |
| **Theorem 2.26** | 126 | Nonempty open subsets of Euclidean spaces can be homeomorphic only in the same dimension. |
| **Theorem 2.27** | 128–130 | The natural map from Δ-complex homology to singular homology is an isomorphism, also for pairs. |

Theorem 2.13 is a source-order trap: it is stated before relative homology and
excision are developed, but its proof uses Theorem 2.20 and Proposition 2.22.
It must not be planned as an early independent theorem.

On pages 127–128 Hatcher records naturality of the long exact sequence of a
pair and of its reduced variant. Those two naturality statements are selected.
The triple sequence and the quotient sequence used with Theorem 2.13 are not.

## Selected slice

The first selected slice decomposes the singular-homology definitions and
Propositions 2.7–2.12. A second fifteen-leaf slice covers the augmented
definition and functoriality of reduced homology, relative chains and homology,
Theorem 2.16, the long exact sequence of a pair and its naturality, Example
2.18, and Proposition 2.19. Its representation is fixed in the
[relative-homology implementation specification](relative-homology-implementation.md).
Eleven of these fifteen leaves are complete. The simplicial-pair foundation is
available at the current pin, and the singular-pair and relative-homology
functors, pair long exact sequence, pair-sequence naturality, and compatible
relative chain homotopy are formalized locally. The pair sequence includes the
integral connecting-map formula. Four downstream leaves remain incomplete; the
pointed comparison, reduced pair sequence, and relative-homology invariance
theorem are ready to state, while reduced-pair-sequence naturality awaits only
the reduced pair sequence.

Proposition 2.6 is deferred because the pinned Mathlib has only the degree-zero
component decomposition. Lemma 2.1, Examples 2.2–2.5, Theorem 2.13, Example
2.17, the triple sequence, excision and quotient-pair comparison, the remaining
sphere applications, invariance of dimension, and the Δ-complex comparison
are later milestones.

For roadmap notation, write
`Hₙ(X; R) := ((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj X`.
Hatcher's integral group `Hₙ(X)` is the specialization to the category of
abelian groups with coefficient object `ℤ`.

## Historical Mathlib `v4.31.0` audit

The original roadmap audit was checked against Mathlib `v4.31.0` at
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

Available exactly:

- `AlgebraicTopology.singularChainComplexFunctor` and
  `AlgebraicTopology.singularHomologyFunctor` in
  `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`.
- `TopCat.singularHomology₀Iso` and `TopCat.singularHomology₀ε` in
  `Mathlib/AlgebraicTopology/SingularHomology/HomologyZero.lean`.
- `AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`
  in `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`.
- `HomologicalComplex.homologyMap` in
  `Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean`.
- `Homotopy.homologyMap_eq` and `HomotopyEquiv.toHomologyIso` in
  `Mathlib/Algebra/Homology/Homotopy.lean`.
- `TopCat.Homotopy.singularChainComplexFunctorObjMap` and
  `TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor` in
  `Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean`.
- `HomologicalComplex.HomologySequence.composableArrows₅_exact` and
  `HomologicalComplex.HomologySequence.δ_naturality` in
  `Mathlib/Algebra/Homology/HomologySequenceLemmas.lean`.

The proof of topological homotopy invariance passes through the singular
simplicial set. It proves Hatcher's theorem, but it does not formalize the
book's explicit prism formula.

Absent from that historical pin were general path-component additivity,
packaged reduced singular homology, relative singular homology, singular
excision, and Δ-complex homology with its comparison theorem.

## Current pin and later work

- Mathlib PR
  [#41285](https://github.com/leanprover-community/mathlib4/pull/41285),
  merged as commit
  [`dbd0e3c605be1c1ac468d358d0815b9183566a8a`](https://github.com/leanprover-community/mathlib4/commit/dbd0e3c605be1c1ac468d358d0815b9183566a8a),
  adds relative homology for simplicial-set pairs and the associated
  exact-sequence API. It is included at this repository's current stable
  Mathlib `v4.34.1` pin.
- Mathlib PR
  [#37659](https://github.com/leanprover-community/mathlib4/pull/37659), an
  older direct relative singular-homology proposal, remains open and is
  superseded in design by the merged simplicial-set-pair API.
- Mathlib PR
  [#41318](https://github.com/leanprover-community/mathlib4/pull/41318), for
  the long exact sequence of a triple, is open and paused pending excision.
- Joël Riou's
  [`excision`](https://github.com/joelriou/excision/tree/8b56cd0c8e5f39a7c2f36418c80b298e469596a6)
  development contains the active subdivision, small-chain, pair, and excision
  design. It is unreleased implementation prior art, not a project dependency.

## Decisions taken

- **Selected boundaries.** Keep the completed 2.7–2.12 spine and add the
  reduced/relative exact-sequence slice described above. Leave the
  excision-dependent and Δ-complex results deferred.
- **Coefficients.** State exact Mathlib nodes with their coefficient-general
  categorical API. Treat Hatcher's integral theory as its abelian-group
  specialization.
- **Proof route.** Accept Mathlib's singular-simplicial-set proof of Theorem
  2.10. Do not claim that Hatcher's prism operator itself is formalized.
- **Reduced theory.** Define reduced homology from Hatcher's augmented complex,
  shifted through `ChainComplex.augment`; do not define it as homology relative
  to a basepoint, since that is Example 2.18.
- **Relative theory.** Use the merged `SSetPair` design. Its foundational node
  is exact Mathlib coverage at the current `v4.34.1` pin, and
  the singular-pair and relative-homology functors, pair long exact sequence,
  pair-sequence naturality, and compatible relative chain homotopy are
  formalized locally, including the connecting-map formula. Use the upstream
  cokernel and exact-sequence APIs for the remaining nodes; do not copy a
  competing cokernel API into the project.
