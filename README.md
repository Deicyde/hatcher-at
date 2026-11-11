# Algebraic Topology (Hatcher)

A Lean 4 formalization of selected results from Allen Hatcher's *Algebraic
Topology*, built on Mathlib. The book's text is not redistributed here.

The main-line chapters and numbered sections are mapped in the
[coverage contract](blueprint/coverage/README.md), not claimed fully
formalized. The selected roadmap now has 350 formalizable leaves: 316 are
complete (298 proved locally and 18 supplied by pinned Mathlib), and 34 are
planned for cellular boundaries and their first computations. The completed
scope includes the selected fundamental-group spines, homology, excision and
quotient applications, degree foundations, all twenty local-degree leaves
through Proposition 2.30, and degree realization and suspension through
Proposition 2.33 and its pole observation.

The completed [degree-realization and suspension milestone](blueprint/roadmap/homology/computations-and-applications/degree-realization-suspension/README.md)
formalizes Examples 2.31–2.32, Proposition 2.33, and arbitrary local degrees at
both suspension poles. All thirty-one leaves are complete, including actual
geometric pinch maps, integer circle powers, the natural suspension boundary,
and every-isolation-witness local-degree equalities.
The completed [cellular-homology milestone](blueprint/roadmap/homology/computations-and-applications/cellular-homology/README.md)
covers Lemma 2.34, the cellular complex and Theorem 2.35 in seventeen formalizable
leaves, including the two explicit sphere generator bridges. The next
[cellular boundary and computation milestone](blueprint/roadmap/homology/computations-and-applications/cellular-boundary/README.md)
adds 34 planned leaves for the attaching-degree formula, general cellular
consequences and the actual projective and sphere-product examples.
Thirteen residual source areas remain queued; lettered additional
topics and exercises remain outside scope.

[Browse the published formalization blueprint](https://deicyde.github.io/hatcher-at/)
or [inspect its Markdown source](blueprint/README.md).

Developed with [AutoformBot](https://github.com/facebookresearch/autoform-bot).

The canonical vault is `blueprint/`. CI uses AutoformBot 0.7.0 at the immutable
commit in `.github/autoform-ref`, which both workflows read. The [source-unit index](blueprint/sources/source-units.json)
preserves the legacy coverage locators, hashes, and article mappings; CI checks
that provenance alongside the current Markdown format.
