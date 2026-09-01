# Coverage contract

This project formalizes results from [Hatcher's *Algebraic Topology*](../sources/hatcher.md).
It does not claim to formalize the book. The whole book is *mapped*: every
chapter and numbered section has a roadmap page recording what it contains and
what Mathlib already provides. The selected §1.1 slice is formalized, and the
selected §1.2 and §1.3 spines are decomposed into formalization units. One
Appendix prerequisite is also decomposed. Mapping is not progress, and a
mapped chapter must never be reported as covered.

| Area | Coverage | Evidence |
| --- | --- | --- |
| §1.1 Basic constructions | `DECOMPOSED` | [Nine fully formalized nodes](../roadmap/fundamental-group/basic-constructions/README.md) cover the selected source results |
| §1.1 results outside the selected slice | `DEFERRED` | Corollaries 1.11 and 1.16, Propositions 1.17 and 1.18, and Lemma 1.19 are reserved for a later §1.1 completion pass |
| Chapter 0, underlying geometric notions | `MAPPED` | [Chapter map](../roadmap/underlying-geometric-notions/README.md) |
| §1.2 selected spine | `DECOMPOSED` | [Van Kampen, wedges, and cell-attachment nodes](../roadmap/fundamental-group/van-kampen/README.md) |
| §1.2 results outside the selected slice | `DEFERRED` | Examples 1.22–1.25, Corollary 1.27, and the geometric remainder of Example 1.29 are reserved for later application milestones |
| §1.3 classification and deck spine | `DECOMPOSED` | [Lifting through Proposition 1.40](../roadmap/fundamental-group/covering-spaces/README.md) |
| §1.3 results outside the selected slice | `DEFERRED` | Example 1.35, permutation classification, and Examples 1.41–1.48 are reserved for later milestones |
| §2.1 Simplicial and singular homology | `MAPPED` | [Section map](../roadmap/homology/simplicial-and-singular/README.md) |
| §2.2 Computations and applications | `MAPPED` | [Section map](../roadmap/homology/computations-and-applications/README.md) |
| §2.3 Formal viewpoint | `MAPPED` | [Section map](../roadmap/homology/formal-viewpoint/README.md) |
| §3.1 Cohomology groups | `MAPPED` | [Section map](../roadmap/cohomology/cohomology-groups/README.md) |
| §3.2 Cup product | `MAPPED` | [Section map](../roadmap/cohomology/cup-product/README.md) |
| §3.3 Poincaré duality | `MAPPED` | [Section map](../roadmap/cohomology/poincare-duality/README.md) |
| §4.1 Homotopy groups | `MAPPED` | [Section map](../roadmap/homotopy-theory/homotopy-groups/README.md) |
| §4.2 Elementary methods | `MAPPED` | [Section map](../roadmap/homotopy-theory/elementary-methods/README.md) |
| §4.3 Connections with cohomology | `MAPPED` | [Section map](../roadmap/homotopy-theory/connections-with-cohomology/README.md) |
| Appendix Proposition A.1 | `DECOMPOSED` | [Compact subsets lie in finite subcomplexes](../roadmap/appendix/compact-subspace-finite-subcomplex.md) |
| Appendix remainder | `MAPPED` | [Appendix map](../roadmap/appendix/README.md) |
| Lettered additional topics | `OUT` | Supplementary sections are outside this project's main-line scope |
| Exercises | `OUT` | Exercise sets are not source targets for this project |

## In scope

[Hatcher §1.1, Basic constructions](../roadmap/fundamental-group/basic-constructions/README.md),
pages 25–38, decomposed into nine nodes. The main target is Theorem 1.7,
`π₁(S¹) ≅ ℤ`. The section's other in-scope results are:

| Node | Source result | Kind |
| --- | --- | --- |
| [The real line covers the circle](../roadmap/fundamental-group/basic-constructions/circle-covering.md) | page 29, unnumbered | bridged |
| [Winding number](../roadmap/fundamental-group/basic-constructions/winding-number.md) | page 29, unnumbered | bridged |
| [Fundamental group of the circle](../roadmap/fundamental-group/basic-constructions/fundamental-group-circle.md) | **Theorem 1.7** | cited |
| [No retraction of the disc](../roadmap/fundamental-group/basic-constructions/no-retraction-disc.md) | page 31, inside Thm 1.9's proof | bridged |
| [Brouwer for the disc](../roadmap/fundamental-group/basic-constructions/brouwer-disc.md) | **Theorem 1.9** | cited |
| [Fundamental theorem of algebra](../roadmap/fundamental-group/basic-constructions/fundamental-theorem-algebra.md) | **Theorem 1.8** | cited |
| [Loop splits across an open cover](../roadmap/fundamental-group/basic-constructions/loop-in-open-cover.md) | **Lemma 1.15** | cited |
| [Higher spheres are simply connected](../roadmap/fundamental-group/basic-constructions/sphere-simply-connected.md) | **Proposition 1.14** | cited |
| [Borsuk–Ulam for `S²`](../roadmap/fundamental-group/basic-constructions/borsuk-ulam-sphere.md) | **Theorem 1.10** | cited |

Two qualifications on what these nodes do and do not prove.

**Theorem 1.8 is already upstream.** Its statement is Mathlib's
`Complex.exists_root`, packaged by `Complex.isAlgClosed`, in
`Analysis/Complex/Polynomial/Basic.lean` and proved by Liouville's theorem.
The local formalization gives a second proof of a known result. It
is in scope as a source target and must not be counted as new Mathlib coverage.
No §1.1 node in this project sets `mathlib: true`.

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
separate cross-chapter node. Two implementation gaps are marked not ready:
Hatcher's threefold-incidence homotopy decomposition and the bridge between
Mathlib's classical and categorical CW-complex APIs. No §1.2 node is claimed
formalized yet.

### §1.3 selected classification and deck spine

[Covering spaces](../roadmap/fundamental-group/covering-spaces/README.md) is
decomposed from homotopy lifting through the subgroup classification of
connected covers. Exact pinned lifting results are separated from local
source-facing wrappers. The path-class universal-cover construction and the
cover-bundling boundary are explicit nodes, with unresolved representation
work marked not ready rather than hidden in the final classification theorem.
The deck-transformation branch continues through the normalizer quotient and
orbit-action calculation in Propositions 1.39–1.40.

### Deferred within §1.1

Corollary 1.11 (`S²` as a union of three closed sets), Corollary 1.16
(`ℝ²` is not homeomorphic to `ℝⁿ` for `n ≠ 2`), Proposition 1.17
(retracts and deformation retracts), Proposition 1.18 (homotopy equivalences
induce fundamental-group isomorphisms), and Lemma 1.19 (the basepoint-change
formula for homotopic maps) are deliberately excluded from this slice. The
latter two have close groupoid-level counterparts in Mathlib, but this project
does not yet provide source-facing declarations for them. §1.1 is therefore
*not* fully covered even when all nine nodes are complete.

## Mapped but not decomposed

Everything else. These pages carry exposition and prior-art notes, and no
formalization nodes:

- Chapter 0, [Some underlying geometric notions](../roadmap/underlying-geometric-notions/README.md)
- Chapter 2, [Homology](../roadmap/homology/README.md), all three sections
- Chapter 3, [Cohomology](../roadmap/cohomology/README.md), all three sections
- Chapter 4, [Homotopy theory](../roadmap/homotopy-theory/README.md), all three sections
- The remainder of the [Appendix](../roadmap/appendix/README.md)

Decomposing any of these is a future roadmap run, not proof work. Within
Chapter 1, Example 1.35, permutation reconstruction, and Examples 1.41–1.48
remain deferred. The next mapped main-line section is §2.1.

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

A node is complete when its named Lean declarations compile, its main result
carries `proof: formalized`, and the proof uses no `sorry` and no axioms beyond
Lean's three. The CI axiom audit is the check.

A section counts as finished only when it is decomposed and every node beneath
it is complete, *and* nothing numbered in it has been deferred. By that rule
§1.1 cannot be reported finished under the current slice, because five
numbered results are deferred. A section that is merely mapped is never
finished, whatever its prose says.

The project as a whole makes no completion claim. Decomposing additional
sections does not by itself imply that their nodes are formalized.
