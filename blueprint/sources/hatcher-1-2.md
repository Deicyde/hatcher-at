# Hatcher §1.2, Van Kampen's Theorem

Numbered results in [Hatcher](hatcher.md) §1.2, pages 40–55. Printed page
numbers are used below; the PDF page is the printed page plus nine.

Statements are paraphrased. Read the actual text in the official PDF.

## Algebraic preparation (40–42)

Hatcher constructs the free product `∗ i, G i` by reduced words and states its
universal property: a family of homomorphisms `G i →* H` extends uniquely to a
homomorphism from the free product. The pinned Mathlib provides this as
`Monoid.CoprodI` and the equivalence `Monoid.CoprodI.lift` in
`Mathlib/GroupTheory/CoprodI.lean`.

## Van Kampen and examples (43–49)

| Result | Page | Paraphrase |
| --- | --- | --- |
| **Theorem 1.20** | 43 | For an arbitrary path-connected open cover with a shared basepoint, path-connected pairwise intersections make the canonical free-product map onto `π₁(X)` surjective; path-connected triple intersections identify its kernel with the normal closure of the overlap relations. |
| Example 1.21 | 43 | The fundamental group of a wedge of path-connected, well-pointed spaces is the free product of their fundamental groups. |
| Example 1.22 | 43–44 | The one-skeleton of a cube has free fundamental group of rank five. |
| Example 1.23 | 46 | The complements of one circle, an unlink, and the pictured standard linked pair of circles have fundamental groups `ℤ`, `ℤ * ℤ`, and `ℤ × ℤ`. |
| Example 1.24 | 47–49 | For coprime positive `m,n`, the `(m,n)` torus-knot complement has group `Gₘ,ₙ = ⟨a, b | a^m = b^n⟩`; for `m,n > 1`, the common power generates its center, the quotient is `ℤ/mℤ * ℤ/nℤ`, and the group recovers the unordered pair `{m,n}`. |
| Example 1.25 | 49 | The shrinking wedge of circles has an uncountable, nonabelian fundamental group. |

The proof of Theorem 1.20 occupies pages 44–46. Its first clause is exactly
the surjectivity argument already isolated as Hatcher's Lemma 1.15. For the
kernel clause, Hatcher subdivides a loop homotopy into rectangles subordinate
to the cover and shows that the factorizations along successive horizontal
cuts differ by elementary moves. Pairwise intersections supply connector
paths; triple intersections make the choices compatible.

## Cell complexes (49–52)

| Result | Page | Paraphrase |
| --- | --- | --- |
| **Proposition 1.26(a)** | 50 | Attaching 2-cells quotients `π₁(X)` by the normal closure of the transported attaching loops. |
| **Proposition 1.26(b)** | 50 | Attaching cells of one fixed dimension greater than two preserves the fundamental group. |
| **Proposition 1.26(c)** | 50 | A path-connected CW complex and its 2-skeleton have isomorphic fundamental groups. |
| Corollary 1.27 | 51 | Closed orientable surfaces of different genera are not homotopy equivalent. |
| Corollary 1.28 | 52 | Every group is the fundamental group of a two-dimensional cell complex. |
| Example 1.29 | 52 | For positive `n`, attaching a 2-cell to `S¹` by the degree-`n` map gives a complex with fundamental group `ℤ/nℤ`; `n = 2` gives `ℝP²`, while for `n > 2` the complex is not a surface and Hatcher discusses its embedding behavior. |

Proposition 1.26(c) also uses Appendix Proposition A.1 (page 520): every
compact subspace of a CW complex lies in a finite subcomplex.

Exercises 1–22 on pages 52–55 remain outside the project's source targets.

## Selected slice

The decomposed spine follows the section's advertised route:

`free products → van Kampen → wedges → cell attachments → every group occurs as π₁`.

Theorem 1.20, Example 1.21, all three parts of Proposition 1.26, Corollary 1.28,
and the group computation in Example 1.29 are selected. Example 1.29's
geometric non-surface remarks are not included.

Examples 1.22–1.25 and Corollary 1.27 are deferred. Their main cost is graph,
knot-complement, wild-space, or surface infrastructure rather than the van
Kampen theorem itself.

## Prior art in the pinned Mathlib

Checked against Mathlib `v4.31.0` at
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

Available ingredients:

- `Monoid.CoprodI`, `Monoid.CoprodI.of`, and the equivalence
  `Monoid.CoprodI.lift` in `Mathlib/GroupTheory/CoprodI.lean` give indexed free
  products and their universal property.
- `Subgroup.normalClosure` and `QuotientGroup.quotientKerEquivOfSurjective`
  provide the algebraic quotient step.
- `FundamentalGroup.map` and `FundamentalGroupoid.map` provide the inclusion
  homomorphisms.
- `exists_monotone_Icc_subset_open_cover_unitInterval_prod_self` in
  `Mathlib/Topology/UnitInterval.lean` supplies the initial rectangular grid
  subordinate to an open cover. Hatcher's further perturbation, which ensures
  that at most three regions meet at a vertex, is not in Mathlib.
- `HomotopicalAlgebra.AttachCells` in
  `Mathlib/AlgebraicTopology/RelativeCellComplex/AttachCells.lean` expresses
  cell attachment as a pushout, and `TopCat.RelativeCWComplex` specializes the
  relative-cell-complex API to disks and spheres.
- `PresentedGroup` in `Mathlib/GroupTheory/PresentedGroup.lean` supplies
  groups by generators and relations.

`Monoid.PushoutI` has one common amalgamating group mapping to every factor.
It models the two-set specialization, but not Theorem 1.20's arbitrary cover
with separate groups for all pairwise intersections. The public theorem will
therefore use `Monoid.CoprodI` modulo the normal closure of Hatcher's overlap
relations.

## Active upstream work

- [Mathlib PR #41603](https://github.com/leanprover-community/mathlib4/pull/41603)
  is a draft groupoid/cosheaf form of van Kampen. Its head is `9a19745b`; it is
  generated, unreviewed, and not in the pinned revision. It is implementation
  prior art for path decomposition, common refinements, homotopy invariance,
  and the colimit proof, not an adopted mathematical source.
- [Mathlib PR #10084](https://github.com/leanprover-community/mathlib4/pull/10084)
  is an older unfinished groupoid draft.
- [Mathlib PR #28246](https://github.com/leanprover-community/mathlib4/pull/28246)
  remains open. This project already adapted its open-cover loop decomposition
  for Hatcher's Lemma 1.15.

None of these open PRs receives `mathlib: true`.

## Decisions taken

- **Public theorem shape.** State Hatcher's shared-basepoint group theorem.
  A groupoid proof may be used internally, but it must discharge the based
  free-product quotient statement rather than replace it.
- **Cover cardinality.** Keep Hatcher's arbitrary indexed cover. Compactness
  produces finite factorizations inside the proof; the theorem is not silently
  restricted to finite covers.
- **Algebraic target.** Use the indexed free product modulo the normal closure
  of pairwise-overlap relations. Do not use `Monoid.PushoutI` for the general
  theorem.
- **Surjectivity.** Reuse
  `Hatcher.loop_homotopic_prod_of_isOpenCover`, the completed Lemma 1.15 node.
- **Wedges.** Introduce a project definition as the quotient of `Σ i, X i`
  with an adjoined wedge point, identifying that point with every chosen
  basepoint. This convention makes the empty wedge a one-point space. Example
  1.21 retains Hatcher's well-pointed hypothesis: each basepoint is a
  deformation retract of an open neighborhood.
- **Homotopy subdivision.** Separate Mathlib's product grid from Hatcher's
  staggered refinement. The latter must ensure that at most three labeled
  regions meet at each vertex, since Theorem 1.20 assumes connectivity only
  for double and triple intersections.
- **Cell attachments.** State Proposition 1.26(a) and (b) against Mathlib's
  pushout-based `HomotopicalAlgebra.AttachCells` API. State Proposition A.1 and
  the 2-skeleton result against the classical `Topology.CWComplex` API. An
  explicit bridge between classical skeleton inclusions and abstract cell
  attachments is a separate, currently not-ready roadmap node; Mathlib records
  this equivalence as a TODO.
- **Source granularity.** Proposition 1.26(a), (b), and (c) are separate nodes.
  Completing one part does not mark the others complete.
