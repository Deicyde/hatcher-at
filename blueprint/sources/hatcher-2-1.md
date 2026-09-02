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
augmented singular chain complex. They are not part of the selected first
slice because the pinned Mathlib has no packaged reduced singular homology.

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

## Selected slice

This pass decomposes the singular-homology definitions and Propositions
2.7–2.12. Proposition 2.6 is deferred because the pinned Mathlib has only the
degree-zero component decomposition. Reduced homology, relative homology,
excision, the sphere calculation, invariance of dimension, and the Δ-complex
comparison are later milestones.

For roadmap notation, write
`Hₙ(X; R) := ((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj X`.
Hatcher's integral group `Hₙ(X)` is the specialization to the category of
abelian groups with coefficient object `ℤ`.

## Prior art in the pinned Mathlib

Checked against Mathlib `v4.31.0` at
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

The proof of topological homotopy invariance passes through the singular
simplicial set. It proves Hatcher's theorem, but it does not formalize the
book's explicit prism formula.

Absent from the pin are general path-component additivity, packaged reduced
singular homology, relative singular homology, singular excision, and
Δ-complex homology with its comparison theorem.

## Post-pin work

- Mathlib PR
  [#41285](https://github.com/leanprover-community/mathlib4/pull/41285),
  merged on 2026-08-31, adds relative homology for simplicial-set pairs and
  the associated exact-sequence API. It is not available at this repository's
  pin.
- Mathlib PR
  [#37659](https://github.com/leanprover-community/mathlib4/pull/37659), an
  older relative singular-homology proposal, remains open after review moved
  the design toward simplicial-set pairs.
- Mathlib PR
  [#41318](https://github.com/leanprover-community/mathlib4/pull/41318), for
  the long exact sequence of a triple, is open and paused pending excision.
- Joël Riou's
  [`excision`](https://github.com/joelriou/excision) development contains the
  active subdivision, small-chain, pair, and excision design. Later roadmap
  work should follow that upstream direction rather than create a competing
  relative-homology architecture.

## Decisions taken

- **First boundary.** Decompose the well-supported 2.7–2.12 spine now. Record
  all other results in §2.1 as deferred.
- **Coefficients.** State exact Mathlib nodes with their coefficient-general
  categorical API. Treat Hatcher's integral theory as its abelian-group
  specialization.
- **Proof route.** Accept Mathlib's singular-simplicial-set proof of Theorem
  2.10. Do not claim that Hatcher's prism operator itself is formalized.
- **Relative theory.** Do not design a local cokernel API against a stale pin.
  Revisit the pin and adopt the merged `SSetPair` design before decomposing
  Theorem 2.16 and relative homology.
