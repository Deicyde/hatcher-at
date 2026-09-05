---
schema: autoform-coverage/v2
artifact: sources/hatcher-execution-scope.txt
artifact_sha256: bd8b33c459ef8c5c7923e54b670a1706fc3f41c3105b6b26f6c9c0ecef1ea24c
---

# Coverage contract

This project formalizes selected results from [Hatcher's *Algebraic Topology*](../sources/hatcher.md); it does not claim to formalize the whole book. The canonical artifact is a project-authored, citation-only execution ledger rather than redistributed book text. Its twenty lines preserve the existing scope: five decomposed source areas, thirteen explicitly deferred areas, and two areas outside scope. Every decomposed row links directly to its formalizable roadmap leaves.

| Unit | Area | Lines | Locator | Unit SHA-256 | Coverage | Evidence |
| --- | --- | --- | --- | --- | --- | --- |
| hatcher-1-1-basic-constructions | §1.1 Basic constructions | 1-1 | Hatcher §1.1, pages 25–38 | d4babbb34e3035c1ee16fbc7e6b707dbf0c17c3cfacf0ef8834756326f8b9a00 | DECOMPOSED | The selected section is decomposed into its explicit source-facing and Mathlib-backed leaves. [Straight-line homotopy between paths](../roadmap/fundamental-group/basic-constructions/affine-path-homotopy.md), [Borsuk–Ulam for the two-sphere](../roadmap/fundamental-group/basic-constructions/borsuk-ulam-sphere.md), [Brouwer's fixed point theorem for the disc](../roadmap/fundamental-group/basic-constructions/brouwer-disc.md), [A path induces change of basepoint](../roadmap/fundamental-group/basic-constructions/change-of-basepoint.md), [The real line covers the circle](../roadmap/fundamental-group/basic-constructions/circle-covering.md), [Convex sets have trivial fundamental group](../roadmap/fundamental-group/basic-constructions/convex-trivial-fundamental-group.md), [Euclidean two-space is distinguished by dimension](../roadmap/fundamental-group/basic-constructions/euclidean-two-not-homeomorphic.md), [The fundamental group of the circle](../roadmap/fundamental-group/basic-constructions/fundamental-group-circle.md), [Path concatenation gives the fundamental-group law](../roadmap/fundamental-group/basic-constructions/fundamental-group-law.md), [The fundamental theorem of algebra](../roadmap/fundamental-group/basic-constructions/fundamental-theorem-algebra.md), [Homotopic maps differ by basepoint change](../roadmap/fundamental-group/basic-constructions/homotopic-maps-fundamental-group.md), [A homotopy equivalence induces a fundamental-group isomorphism](../roadmap/fundamental-group/basic-constructions/homotopy-equivalence-fundamental-group.md), [A loop splits across an open cover](../roadmap/fundamental-group/basic-constructions/loop-in-open-cover.md), [The circle is not a retract of the disc](../roadmap/fundamental-group/basic-constructions/no-retraction-disc.md), [Path homotopy is an equivalence relation](../roadmap/fundamental-group/basic-constructions/path-homotopy-equivalence.md), [The fundamental group of a product](../roadmap/fundamental-group/basic-constructions/product-fundamental-group.md), [Retractions and deformation retracts on the fundamental group](../roadmap/fundamental-group/basic-constructions/retractions-fundamental-group.md), [Simply connected spaces have unique path-homotopy classes](../roadmap/fundamental-group/basic-constructions/simply-connected-unique-path-classes.md), [Higher spheres are simply connected](../roadmap/fundamental-group/basic-constructions/sphere-simply-connected.md), [Three closed sets covering the sphere contain an antipodal pair](../roadmap/fundamental-group/basic-constructions/three-closed-sets-antipodal.md), [The fundamental group of the torus](../roadmap/fundamental-group/basic-constructions/torus-fundamental-group.md), [Winding number of a loop in the circle](../roadmap/fundamental-group/basic-constructions/winding-number.md) |
| chapter-0-underlying-geometric-notions | Chapter 0, underlying geometric notions | 2-2 | Hatcher Chapter 0, pages 1–20 | 0c3060a7dd102a89e57b59c842194aa76f56691f210b8e7becdb3ea196da6d21 | DEFERRED | Deferred to a future roadmap milestone; the current chapter page is an informational map. |
| hatcher-1-2-selected-spine | §1.2 selected spine | 3-3 | Hatcher §1.2, pages 40–55 | 6743c757054319ea82b98fd0c8e7ae9d405b7f22117053bda8573a635dacc8a9 | DECOMPOSED | The selected van Kampen, wedge, cell-attachment, and classical-CW bridge spine is decomposed into formalizable leaves. [Classical skeleton inclusions are abstract cell attachments](../roadmap/appendix/classical-skeleton-cell-attachment.md), [Attaching higher cells preserves the fundamental group](../roadmap/fundamental-group/van-kampen/attach-higher-cells-fundamental-group.md), [Attaching 2-cells adds the attaching relations](../roadmap/fundamental-group/van-kampen/attach-two-cells-fundamental-group.md), [The attaching-sphere pieces generate the intersection group](../roadmap/fundamental-group/van-kampen/attaching-spheres-generate-intersection.md), [Binary van Kampen is a group pushout](../roadmap/fundamental-group/van-kampen/binary-van-kampen-pushout.md), [An open-cover model for attached cells](../roadmap/fundamental-group/van-kampen/cell-attachment-cover-model.md), [A binary cover with a contractible second piece](../roadmap/fundamental-group/van-kampen/cell-attachment-support/binary-cover-contractible-piece.md), [A binary cover with a trivial second fundamental group](../roadmap/fundamental-group/van-kampen/cell-attachment-support/binary-cover-trivial-piece-quotient.md), [The degree-n circle map sends the generator to the degree-n loop](../roadmap/fundamental-group/van-kampen/cell-attachment-support/circle-degree-map.md), [The circle is well-pointed at one](../roadmap/fundamental-group/van-kampen/cell-attachment-support/circle-well-pointed.md), [The cone on a disk boundary is the disk](../roadmap/fundamental-group/van-kampen/cell-attachment-support/cone-disk-homeomorphism.md), [The degree-n circle relation gives the cyclic group](../roadmap/fundamental-group/van-kampen/cell-attachment-support/cyclic-relation-quotient.md), [An indexed family of cones has a two-set open cover](../roadmap/fundamental-group/van-kampen/cell-attachment-support/indexed-cone-open-cover.md), [A single cone attachment is a standard cell attachment](../roadmap/fundamental-group/van-kampen/cell-attachment-support/single-basic-cell-attachment.md), [The base-side cone cover retracts onto the original space](../roadmap/fundamental-group/van-kampen/cell-attachment-support/single-cone-base-retract.md), [The single-cone cover intersection has the homotopy type of its boundary](../roadmap/fundamental-group/van-kampen/cell-attachment-support/single-cone-intersection.md), [A single cone attachment has a two-set open cover](../roadmap/fundamental-group/van-kampen/cell-attachment-support/single-cone-open-cover.md), [A single cone attachment is a topological pushout](../roadmap/fundamental-group/van-kampen/cell-attachment-support/single-cone-pushout.md), [The cone-side cover member is contractible](../roadmap/fundamental-group/van-kampen/cell-attachment-support/single-cone-upper-contractible.md), [Cover factorizations of a loop](../roadmap/fundamental-group/van-kampen/cover-factorization.md), [The group presentation associated to an open cover](../roadmap/fundamental-group/van-kampen/cover-group-presentation.md), [Overlap relations vanish under the cover map](../roadmap/fundamental-group/van-kampen/cover-map-relations.md), [The cyclic presentation complex](../roadmap/fundamental-group/van-kampen/cyclic-presentation-complex.md), [Every group is a fundamental group](../roadmap/fundamental-group/van-kampen/every-group-fundamental-group.md), [Every group admits a generators-and-relations presentation](../roadmap/fundamental-group/van-kampen/every-group-presentation.md), [Elementary factorization moves preserve the quotient class](../roadmap/fundamental-group/van-kampen/factorization-moves.md), [Homotopic factorizations have the same quotient class](../roadmap/fundamental-group/van-kampen/homotopic-factorizations.md), [A homotopy admits a threefold-incidence cover decomposition](../roadmap/fundamental-group/van-kampen/homotopy-cover-decomposition.md), [The pointed wedge of a family of spaces](../roadmap/fundamental-group/van-kampen/pointed-wedge.md), [Presented groups have two-dimensional presentation complexes](../roadmap/fundamental-group/van-kampen/presentation-complex-realization.md), [The 2-skeleton determines the fundamental group](../roadmap/fundamental-group/van-kampen/two-skeleton-fundamental-group.md), [The kernel is generated by overlap relations](../roadmap/fundamental-group/van-kampen/van-kampen-kernel.md), [Van Kampen's quotient isomorphism](../roadmap/fundamental-group/van-kampen/van-kampen-quotient.md), [The van Kampen cover map is surjective](../roadmap/fundamental-group/van-kampen/van-kampen-surjective.md), [The fundamental group of a wedge of circles](../roadmap/fundamental-group/van-kampen/wedge-circles-free-group.md), [The fundamental group of a wedge](../roadmap/fundamental-group/van-kampen/wedge-fundamental-group.md), [The standard cover of a well-pointed wedge](../roadmap/fundamental-group/van-kampen/well-pointed-wedge-cover.md) |
| hatcher-1-2-deferred-remainder | §1.2 results outside the selected slice | 4-4 | Hatcher §1.2, pages 40–55 | 069343d0d5c388320af4a0fa3cd598b8db46f34ec6803b3c3c7fd1c46e3f90eb | DEFERRED | Examples 1.22–1.25, Corollary 1.27, and the geometric remainder of Example 1.29 are reserved for later application milestones. |
| hatcher-1-3-selected-spine | §1.3 classification and deck spine | 5-5 | Hatcher §1.3, pages 56–82 | 881efdeb7a6e4db559c43675606e17063b7cfd6d3f1330c94de8e83c6536ed61 | DECOMPOSED | The selected lifting, universal-cover, classification, and deck-transformation spine is decomposed into formalizable leaves. [Pointed connected covering spaces](../roadmap/fundamental-group/covering-spaces/based-connected-cover.md), [The induced subgroup consists of loops with closed lifts](../roadmap/fundamental-group/covering-spaces/closed-lift-image.md), [Changing the lifted basepoint conjugates the image subgroup](../roadmap/fundamental-group/covering-spaces/cover-basepoint-conjugacy.md), [Covering maps inject path-homotopy classes](../roadmap/fundamental-group/covering-spaces/covering-injective-path-classes.md), [Covering-space actions give quotient coverings](../roadmap/fundamental-group/covering-spaces/deck-transformations/covering-space-action.md), [The deck group is the normalizer quotient](../roadmap/fundamental-group/covering-spaces/deck-transformations/deck-group-calculation.md), [A deck transformation is determined by one lifted point](../roadmap/fundamental-group/covering-spaces/deck-transformations/deck-realization.md), [Deck transformations and normal covers](../roadmap/fundamental-group/covering-spaces/deck-transformations/deck-transformation-group.md), [The normalizer acts by deck transformations](../roadmap/fundamental-group/covering-spaces/deck-transformations/normalizer-to-deck.md), [The normalizer map is surjective with kernel the covering subgroup](../roadmap/fundamental-group/covering-spaces/deck-transformations/normalizer-to-deck-exactness.md), [Orbit quotients are normal and have the expected deck group](../roadmap/fundamental-group/covering-spaces/deck-transformations/orbit-quotient-deck-group.md), [The orbit-quotient fundamental group recovers the acting group](../roadmap/fundamental-group/covering-spaces/deck-transformations/orbit-quotient-fundamental-group.md), [Homotopies lift uniquely through a covering map](../roadmap/fundamental-group/covering-spaces/homotopy-lifting.md), [A map lifts exactly when its fundamental group lands in the covering subgroup](../roadmap/fundamental-group/covering-spaces/lifting-criterion.md), [Local path-connectedness ascends along a covering](../roadmap/fundamental-group/covering-spaces/locally-path-connected-total-space.md), [The fundamental group acts on a covering fiber](../roadmap/fundamental-group/covering-spaces/monodromy-action.md), [Pointed connected covers are classified by subgroups](../roadmap/fundamental-group/covering-spaces/pointed-cover-classification.md), [Equal image subgroups characterize pointed cover isomorphism](../roadmap/fundamental-group/covering-spaces/pointed-cover-rigidity.md), [Sheets are cosets of the induced subgroup](../roadmap/fundamental-group/covering-spaces/sheet-index.md), [The subgroup cover realizes the chosen subgroup](../roadmap/fundamental-group/covering-spaces/subgroup-cover-image.md), [The subgroup projection is a path-connected covering](../roadmap/fundamental-group/covering-spaces/subgroup-cover-is-covering.md), [The covering space associated to a subgroup](../roadmap/fundamental-group/covering-spaces/subgroup-cover-space.md), [A lift is determined by one point](../roadmap/fundamental-group/covering-spaces/unique-lifting.md), [A simply-connected cover maps uniquely to every pointed connected cover](../roadmap/fundamental-group/covering-spaces/universal-cover-initial.md), [Small nullhomotopy neighborhoods form a basis](../roadmap/fundamental-group/covering-spaces/universal-cover/nullhomotopic-open-basis.md), [Semilocally simply-connected spaces](../roadmap/fundamental-group/covering-spaces/universal-cover/semilocally-simply-connected.md), [Universal-cover basis](../roadmap/fundamental-group/covering-spaces/universal-cover/universal-cover-basis.md), [The endpoint map is a covering](../roadmap/fundamental-group/covering-spaces/universal-cover/universal-cover-is-covering.md), [The path-class cover is path-connected](../roadmap/fundamental-group/covering-spaces/universal-cover/universal-cover-path-connected.md), [The path-class universal-cover space](../roadmap/fundamental-group/covering-spaces/universal-cover/universal-cover-path-space.md), [The path-class cover is simply-connected](../roadmap/fundamental-group/covering-spaces/universal-cover/universal-cover-simply-connected.md), [Connected covers are classified by conjugacy classes](../roadmap/fundamental-group/covering-spaces/unpointed-cover-classification.md) |
| hatcher-1-3-deferred-remainder | §1.3 results outside the selected slice | 6-6 | Hatcher §1.3, pages 56–82 | fa7d018b262c5f5800109b7c49e3f950f0bdccdd71952a41a1e06bf823f6efac | DEFERRED | Example 1.35, permutation classification, and Examples 1.41–1.48 are reserved for later milestones. |
| hatcher-2-1-selected-spine | §2.1 singular-homology functoriality spine | 7-7 | Hatcher §2.1, pages 102–133 | 6d7497c44b12dc33b5df9d8dcf523a958b4f727b0d7908ea0e8e3badfdd347c6 | DECOMPOSED | The selected singular-chain, homology, and homotopy-invariance spine is decomposed into formalizable leaves. [Chain-homotopic maps induce the same homology map](../roadmap/homology/simplicial-and-singular/chain-homotopy-invariance.md), [A chain map induces a map on homology](../roadmap/homology/simplicial-and-singular/chain-map-homology.md), [A homotopy equivalence induces homology isomorphisms](../roadmap/homology/simplicial-and-singular/homotopy-equivalence-homology-iso.md), [Homology of a point](../roadmap/homology/simplicial-and-singular/point-homology.md), [The singular chain complex](../roadmap/homology/simplicial-and-singular/singular-chain-complex.md), [Singular homology](../roadmap/homology/simplicial-and-singular/singular-homology.md), [Homotopic maps induce the same singular-homology map](../roadmap/homology/simplicial-and-singular/singular-homology-homotopy-invariance.md), [A topological homotopy gives a singular-chain homotopy](../roadmap/homology/simplicial-and-singular/topological-homotopy-chain-homotopy.md), [Higher homology vanishes for totally disconnected spaces](../roadmap/homology/simplicial-and-singular/totally-disconnected-higher-homology.md), [Zeroth homology is free on path components](../roadmap/homology/simplicial-and-singular/zeroth-homology-components.md) |
| hatcher-2-1-deferred-remainder | §2.1 results outside the selected slice | 8-8 | Hatcher §2.1, pages 102–133 | 5ca149267ef79ec4308ff9d663cf8d552613a63c45e8a2d822207d61eced218d | DEFERRED | Proposition 2.6, Δ-complex homology, reduced and relative homology, excision, sphere applications, invariance of dimension, and the comparison theorem are reserved for later milestones. |
| hatcher-2-2-computations-applications | §2.2 Computations and applications | 9-9 | Hatcher §2.2, pages 134–159 | f02ccfbe89d7abc56b787b447540b12bd88abaac20aa4838a119d63092ef6d8d | DEFERRED | Deferred to a future roadmap milestone; the current section page is an informational map. |
| hatcher-2-3-formal-viewpoint | §2.3 Formal viewpoint | 10-10 | Hatcher §2.3, pages 160–165 | d1104663ca164b82f33fd006b55060c996c602330693bfec4e61eba22530d4d7 | DEFERRED | Deferred to a future roadmap milestone; the current section page is an informational map. |
| hatcher-3-1-cohomology-groups | §3.1 Cohomology groups | 11-11 | Hatcher §3.1, pages 190–205 | 2b86cf2a2b961dd0eb7abaad041fb0b2323aa483988ebad9cf4934d250aca917 | DEFERRED | Deferred to a future roadmap milestone; the current section page is an informational map. |
| hatcher-3-2-cup-product | §3.2 Cup product | 12-12 | Hatcher §3.2, pages 206–229 | 9a816e99214134d16abfbabaa5b144b63f86513a80c9d0360be23121723f684f | DEFERRED | Deferred to a future roadmap milestone; the current section page is an informational map. |
| hatcher-3-3-poincare-duality | §3.3 Poincaré duality | 13-13 | Hatcher §3.3, pages 230–260 | c9730782969b87332484c53febccb30ff3cc5dac191a40e4ff66a1ceb386d552 | DEFERRED | Deferred to a future roadmap milestone; the current section page is an informational map. |
| hatcher-4-1-homotopy-groups | §4.1 Homotopy groups | 14-14 | Hatcher §4.1, pages 339–359 | fec386b117eff960f6af60f3ce0b6f7ba78bc098b450ae4cef69248167cc6fcb | DEFERRED | Deferred to a future roadmap milestone; the current section page is an informational map. |
| hatcher-4-2-elementary-methods | §4.2 Elementary methods | 15-15 | Hatcher §4.2, pages 360–392 | e4e973e0c9d493c2f6ca59f1837bde6b4953e69df966a1d2f2d6fccd9f47aa53 | DEFERRED | Deferred to a future roadmap milestone; the current section page is an informational map. |
| hatcher-4-3-connections-cohomology | §4.3 Connections with cohomology | 16-16 | Hatcher §4.3, pages 393–420 | 3ff5e03e3ad165c3bad3234eb9670b1626ba3ab281f9f475f46cc494b052d134 | DEFERRED | Deferred to a future roadmap milestone; the current section page is an informational map. |
| appendix-proposition-a-1 | Appendix Proposition A.1 | 17-17 | Hatcher Appendix, Proposition A.1 | 974df7bb29f1375f810ff98cbde04e99fb81f1615e1a1637cf9cd987783030fa | DECOMPOSED | The compact-subspace theorem is represented by its source-facing formalization leaf. [Compact subsets lie in finite subcomplexes](../roadmap/appendix/compact-subspace-finite-subcomplex.md) |
| appendix-remainder | Appendix remainder | 18-18 | Hatcher Appendix after Proposition A.1 | 1116cfc2204f9412dabc447a0b5c48a1e17c72a1b8c96f521bb5698e5120482d | DEFERRED | Deferred to a future roadmap milestone; the current appendix page is an informational map. |
| lettered-additional-topics | Lettered additional topics | 19-19 | Hatcher §§1.A–4.L | 16905334d7dfc5520f9f89e337877212520b3800f320ecd22099601478df6a02 | OUT | Supplementary lettered sections are outside this project's main-line scope. |
| exercises | Exercises | 20-20 | Exercise sets throughout Hatcher | 6b62bc779713d6145d530fd369f5e6dfa8c241f508a7a4138ad3874d520a0fe7 | OUT | Exercise sets are not source targets for this project. |

## In scope

[Hatcher §1.1, Basic constructions](../roadmap/fundamental-group/basic-constructions/README.md),
pages 25–38, decomposed into twenty-two explicit nodes. The main target is Theorem 1.7,
`π₁(S¹) ≅ ℤ`. The section's other in-scope results are:

| Node | Source result | Kind |
| --- | --- | --- |
| [Straight-line homotopy between paths](../roadmap/fundamental-group/basic-constructions/affine-path-homotopy.md) | **Example 1.1** | cited |
| [Path homotopy is an equivalence relation](../roadmap/fundamental-group/basic-constructions/path-homotopy-equivalence.md) | **Proposition 1.2** | pinned Mathlib |
| [Path concatenation gives the fundamental-group law](../roadmap/fundamental-group/basic-constructions/fundamental-group-law.md) | **Proposition 1.3** | cited |
| [Convex sets have trivial fundamental group](../roadmap/fundamental-group/basic-constructions/convex-trivial-fundamental-group.md) | **Example 1.4** | pinned Mathlib bridge |
| [A path induces change of basepoint](../roadmap/fundamental-group/basic-constructions/change-of-basepoint.md) | **Proposition 1.5** | pinned Mathlib |
| [Simply connected spaces have unique path-homotopy classes](../roadmap/fundamental-group/basic-constructions/simply-connected-unique-path-classes.md) | **Proposition 1.6** | pinned Mathlib |
| [The real line covers the circle](../roadmap/fundamental-group/basic-constructions/circle-covering.md) | page 29, unnumbered | bridged |
| [Winding number](../roadmap/fundamental-group/basic-constructions/winding-number.md) | page 29, unnumbered | bridged |
| [Fundamental group of the circle](../roadmap/fundamental-group/basic-constructions/fundamental-group-circle.md) | **Theorem 1.7** | cited |
| [No retraction of the disc](../roadmap/fundamental-group/basic-constructions/no-retraction-disc.md) | page 31, inside Thm 1.9's proof | bridged |
| [Brouwer for the disc](../roadmap/fundamental-group/basic-constructions/brouwer-disc.md) | **Theorem 1.9** | cited |
| [Fundamental theorem of algebra](../roadmap/fundamental-group/basic-constructions/fundamental-theorem-algebra.md) | **Theorem 1.8** | cited |
| [The fundamental group of a product](../roadmap/fundamental-group/basic-constructions/product-fundamental-group.md) | **Proposition 1.12** | cited |
| [The fundamental group of the torus](../roadmap/fundamental-group/basic-constructions/torus-fundamental-group.md) | **Example 1.13** | cited |
| [Loop splits across an open cover](../roadmap/fundamental-group/basic-constructions/loop-in-open-cover.md) | **Lemma 1.15** | cited |
| [Higher spheres are simply connected](../roadmap/fundamental-group/basic-constructions/sphere-simply-connected.md) | **Proposition 1.14** | cited |
| [Borsuk–Ulam for `S²`](../roadmap/fundamental-group/basic-constructions/borsuk-ulam-sphere.md) | **Theorem 1.10** | cited |
| [Three closed sets covering the sphere contain an antipodal pair](../roadmap/fundamental-group/basic-constructions/three-closed-sets-antipodal.md) | **Corollary 1.11** | cited |
| [Euclidean two-space is distinguished by dimension](../roadmap/fundamental-group/basic-constructions/euclidean-two-not-homeomorphic.md) | **Corollary 1.16** | cited |
| [Retractions and deformation retracts on the fundamental group](../roadmap/fundamental-group/basic-constructions/retractions-fundamental-group.md) | **Proposition 1.17** | cited |
| [A homotopy equivalence induces a fundamental-group isomorphism](../roadmap/fundamental-group/basic-constructions/homotopy-equivalence-fundamental-group.md) | **Proposition 1.18** | cited |
| [Homotopic maps differ by basepoint change](../roadmap/fundamental-group/basic-constructions/homotopic-maps-fundamental-group.md) | **Lemma 1.19** | cited |

Three qualifications on what these nodes do and do not prove.

**The opening results are explicit nodes.** Propositions 1.2, 1.5, and 1.6
track the exact pinned declarations `Path.Homotopic.equivalence`,
`FundamentalGroup.fundamentalGroupMulEquivOfPath`, and
`simply_connected_iff_unique_homotopic`. Example 1.4 tracks the exact stronger
input `Convex.contractibleSpace`; `SimplyConnectedSpace.ofContractible` and
Mathlib's subsingleton fundamental-group instance give Hatcher's conclusion.
Example 1.1 and Proposition 1.3 are local formalizations because they record
Hatcher's explicit affine homotopy and left-then-right concatenation
convention.

**Theorem 1.8 is already upstream.** Its statement is Mathlib's
`Complex.exists_root`, packaged by `Complex.isAlgClosed`, in
`Analysis/Complex/Polynomial/Basic.lean` and proved by Liouville's theorem.
The local formalization gives a second proof of a known result. It
is in scope as a source target and must not be counted as new Mathlib coverage.

**Lemma 1.15 is reused by §1.2.** It was formalized locally because
Proposition 1.14 needed it, and it now supplies the surjectivity clause of
Theorem 1.20 exactly as in Hatcher. The proof is adapted from the matching
implementation in open Mathlib PR #28246. The overlap is recorded on
[the node](../roadmap/fundamental-group/basic-constructions/loop-in-open-cover.md).

### §1.2 selected spine

[Van Kampen's theorem](../roadmap/fundamental-group/van-kampen/README.md) is
decomposed from its free-product presentation through the kernel calculation,
wedge sums, cell attachments, and Corollary 1.28. Proposition 1.26 is split by
part, and the Appendix compactness lemma needed for its 2-skeleton clause is a
separate cross-chapter node. The cover presentation, threefold-incidence
homotopy decomposition, and quotient form of van Kampen's theorem are
formalized, as are the pointed-wedge theorem, the higher-cell binary-cover
algebra, the circle's well-pointed neighborhood, and the cyclic quotient
calculation. The point-set cell-attachment model and the bridge between
Mathlib's classical and categorical CW-complex APIs remain not ready.

### §1.3 selected classification and deck spine

[Covering spaces](../roadmap/fundamental-group/covering-spaces/README.md) is
decomposed from homotopy lifting through the subgroup classification of
connected covers. Exact pinned lifting results are separated from local
source-facing wrappers. The path-class universal-cover construction and the
cover-bundling boundary are explicit nodes, with unresolved representation
work marked not ready rather than hidden in the final classification theorem.
The deck-transformation branch continues through the normalizer quotient and
orbit-action calculation in Propositions 1.39–1.40.

### §2.1 selected functoriality spine

[Simplicial and singular homology](../roadmap/homology/simplicial-and-singular/README.md)
is decomposed through the singular-chain and singular-homology definitions,
the exact `H₀` calculation, the point calculation, induced maps, chain-homotopy
invariance, topological homotopy invariance, and Corollary 2.11. Eight nodes
are exact declarations in the pinned Mathlib; the point calculation and
homotopy-equivalence corollary are formalized locally. The project does not
claim Hatcher's explicit prism formula is formalized.

## Deferred roadmap expansion

The remaining high-level section maps are explicitly deferred to future roadmap runs.
These pages carry exposition and prior-art notes, and no formalization nodes:

- Chapter 0, [Some underlying geometric notions](../roadmap/underlying-geometric-notions/README.md)
- Chapter 2, [Homology](../roadmap/homology/README.md), §§2.2–2.3
- Chapter 3, [Cohomology](../roadmap/cohomology/README.md), all three sections
- Chapter 4, [Homotopy theory](../roadmap/homotopy-theory/README.md), all three sections
- The remainder of the [Appendix](../roadmap/appendix/README.md)

Decomposing any of these is a future roadmap run, not proof work. Within
Chapter 1, Example 1.35, permutation reconstruction, and Examples 1.41–1.48
remain deferred. The remainder of §2.1 and the later main-line sections are
explicitly deferred as well.

## Out of scope

- **Lettered Additional Topics.** Sections 1.A, 1.B, 2.A–2.C, 3.A–3.H, and
  4.A–4.L are excluded and have no roadmap pages. They are supplementary in the
  book and would double the mapping effort for material the main line does not
  depend on.
- **Exercises.** Hatcher's exercise sets are not source targets.
- **Reproducing the text.** The book is copyrighted and this repository is
  public, so `/sources/` is gitignored. Source notes carry coordinates and
  one-line paraphrases only.

## Done means

A local node is complete when its named Lean declarations compile, its main
result carries `proof: formalized`, and the proof uses no `sorry` and no axioms
beyond Lean's three. A Mathlib-backed node is complete when its exact pinned
declaration, kind, and declaring file pass provenance checks. CI performs both
checks.

A section counts as finished only when it is decomposed and every node beneath
it is complete, *and* nothing numbered in it has been deferred. By that rule
§1.1 is finished. A section that is merely mapped is never finished, whatever
its prose says.

The project as a whole makes no completion claim. Decomposing additional
sections does not by itself imply that their nodes are formalized.
