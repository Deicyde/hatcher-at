# Algebraic Topology (Hatcher)

A Lean 4 formalization of selected results from Allen Hatcher's *Algebraic
Topology*, built on Mathlib. The book's text is not redistributed here.

The main-line chapters and numbered sections are mapped in the
[coverage contract](blueprints/hatcher/coverage/README.md), not claimed fully
formalized. The selected roadmap has 299 formalizable leaves: 268 are complete
(250 proved locally and 18 supplied by pinned Mathlib), and 31 are newly
planned. The completed scope includes the selected fundamental-group spines,
homology, excision and quotient applications, degree foundations, and all
twenty local-degree leaves through Proposition 2.30.

The new [degree-realization and suspension milestone](blueprints/hatcher/roadmap/homology/computations-and-applications/degree-realization-suspension/README.md)
decomposes Examples 2.31–2.32, Proposition 2.33, and arbitrary local degrees at
suspension poles. Its three construction branches reuse the proved signed
degree-sum formula. Thirteen other source areas remain queued; lettered
additional topics and exercises remain outside scope.

[Browse the published formalization blueprint](https://deicyde.github.io/hatcher-at/)
or [inspect its Markdown source](blueprints/hatcher/README.md).

Developed with [AutoformBot](https://github.com/facebookresearch/autoform-bot).
