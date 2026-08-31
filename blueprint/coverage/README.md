# Coverage contract

This project formalizes results from [Hatcher's *Algebraic Topology*](../sources/hatcher.md).
It does not claim to formalize the book. The whole book is *mapped*: every
chapter and numbered section has a roadmap page recording what it contains and
what Mathlib already provides. Exactly one section is *decomposed* into
formalization nodes. Mapping is not progress, and a mapped chapter must never
be reported as covered.

| Area | Coverage | Evidence |
| --- | --- | --- |
| §1.1 Basic constructions | `DECOMPOSED` | [Nine formalization nodes](../roadmap/fundamental-group/basic-constructions/README.md) cover the selected source results |
| §1.1 deferred corollaries | `DEFERRED` | Corollaries 1.11 and 1.16 are reserved for a later §1.1 completion pass |
| Chapter 0, underlying geometric notions | `MAPPED` | [Chapter map](../roadmap/underlying-geometric-notions/README.md) |
| §1.2 Van Kampen's theorem | `MAPPED` | [Section map](../roadmap/fundamental-group/van-kampen/README.md) |
| §1.3 Covering spaces | `MAPPED` | [Section map](../roadmap/fundamental-group/covering-spaces/README.md) |
| §2.1 Simplicial and singular homology | `MAPPED` | [Section map](../roadmap/homology/simplicial-and-singular/README.md) |
| §2.2 Computations and applications | `MAPPED` | [Section map](../roadmap/homology/computations-and-applications/README.md) |
| §2.3 Formal viewpoint | `MAPPED` | [Section map](../roadmap/homology/formal-viewpoint/README.md) |
| §3.1 Cohomology groups | `MAPPED` | [Section map](../roadmap/cohomology/cohomology-groups/README.md) |
| §3.2 Cup product | `MAPPED` | [Section map](../roadmap/cohomology/cup-product/README.md) |
| §3.3 Poincaré duality | `MAPPED` | [Section map](../roadmap/cohomology/poincare-duality/README.md) |
| §4.1 Homotopy groups | `MAPPED` | [Section map](../roadmap/homotopy-theory/homotopy-groups/README.md) |
| §4.2 Elementary methods | `MAPPED` | [Section map](../roadmap/homotopy-theory/elementary-methods/README.md) |
| §4.3 Connections with cohomology | `MAPPED` | [Section map](../roadmap/homotopy-theory/connections-with-cohomology/README.md) |
| Appendix | `MAPPED` | [Appendix map](../roadmap/appendix/README.md) |
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

Two qualifications on what these nodes will and will not have proved.

**Theorem 1.8 is already upstream.** Its statement is Mathlib's
`Complex.isAlgClosed` in `Analysis/Complex/Polynomial/Basic.lean`, proved by
Liouville's theorem. Formalizing Hatcher's derivation produces a second proof
of a known result. It is in scope as a source target and must not be counted as
new Mathlib coverage. No node in this project sets `mathlib: true`.

**Lemma 1.15 will likely be superseded.** It is formalized here because
Proposition 1.14 needs it, but §1.2's van Kampen theorem subsumes it, so the
§1.2 run will probably generalize the statement rather than reuse it. This is
accepted duplication, recorded on
[the §1.2 page](../roadmap/fundamental-group/van-kampen/README.md).

### Deferred within §1.1

Corollary 1.11 (`S²` as a union of three closed sets) and Corollary 1.16
(`ℝ²` is not homeomorphic to `ℝⁿ` for `n ≠ 2`) are the section's remaining
numbered results. Both are short given the nodes above, and both are
deliberately excluded from this slice. §1.1 is therefore *not* fully covered
even when all nine nodes are complete.

## Mapped but not decomposed

Everything else. These pages carry exposition and prior-art notes, and no
formalization nodes:

- Chapter 0, [Some underlying geometric notions](../roadmap/underlying-geometric-notions/README.md)
- Chapter 1 §1.2 [Van Kampen's theorem](../roadmap/fundamental-group/van-kampen/README.md)
  and §1.3 [Covering spaces](../roadmap/fundamental-group/covering-spaces/README.md)
- Chapter 2, [Homology](../roadmap/homology/README.md), all three sections
- Chapter 3, [Cohomology](../roadmap/cohomology/README.md), all three sections
- Chapter 4, [Homotopy theory](../roadmap/homotopy-theory/README.md), all three sections
- The [Appendix](../roadmap/appendix/README.md)

Decomposing any of these is a future roadmap run, not proof work. §1.2 and §1.3
are the intended next candidates, since they complete Chapter 1.

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
§1.1 cannot be reported finished under the current slice, because Corollaries
1.11 and 1.16 are deferred. A section that is merely mapped is never finished,
whatever its prose says.

The project as a whole makes no completion claim and will not until more than
one section is decomposed.
