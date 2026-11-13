---
article_id: af_018beb3e9d962f2092677b89
---

# Algebraic Topology (Hatcher) roadmap

Formalize selected results from Hatcher's *Algebraic Topology* in Lean 4 on
Mathlib, working outward from the fundamental group. Chapters follow the
book's order; fine leaves expose the actual source objects and maps.

The completed scope contains 319 formalizable leaves: 301 proved locally and
18 supplied by pinned Mathlib. It includes the selected fundamental-group
spines, homology and excision applications, degree foundations, all twenty
local-degree leaves through Proposition 2.30, and the completed thirty-one-leaf
[degree-realization and suspension milestone](homology/computations-and-applications/degree-realization-suspension/README.md).

The completed [cellular-homology milestone](homology/computations-and-applications/cellular-homology/README.md)
proves all seventeen leaves through Lemma 2.34 and Theorem 2.35, including the
explicit sphere generator bridges. The next
[cellular boundary and computation milestone](homology/computations-and-applications/cellular-boundary/README.md)
contains 34 leaves on printed pages 140–141, with the finite geometric
support on pages 6–8. Its no-cells homology, sparse-cell differential and cell-basis results
are complete. The selected DAG therefore has 350 formalizable leaves,
319 complete and 31 planned.

The [coverage contract](../coverage/README.md) maps the whole main-line source
and retains thirteen queued areas; it does not call them exclusions or
external blockers. Lettered additional topics and exercises remain outside
scope. [Source notes](../sources/hatcher.md) fix the citation scheme.

## Chapters

- [Some underlying geometric notions](underlying-geometric-notions/README.md)
- [The fundamental group](fundamental-group/README.md)
- [Homology](homology/README.md)
- [Cohomology](cohomology/README.md)
- [Homotopy theory](homotopy-theory/README.md)
- [Appendix](appendix/README.md)
