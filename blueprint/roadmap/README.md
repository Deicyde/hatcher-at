---
article_id: af_018beb3e9d962f2092677b89
---

# Algebraic Topology (Hatcher) roadmap

Formalize selected results from Hatcher's *Algebraic Topology* in Lean 4 on
Mathlib, working outward from the fundamental group. Chapters follow the
book's order; fine leaves expose the actual source objects and maps.

The completed scope contains 270 formalizable leaves: 252 proved locally and
18 supplied by pinned Mathlib. It includes the selected fundamental-group
spines, homology and excision applications, degree foundations, and all twenty
local-degree leaves through Proposition 2.30, plus the germ-invariance and
singleton-fiber comparisons. The thirty-one-leaf
[degree-realization and suspension milestone](homology/computations-and-applications/degree-realization-suspension/README.md)
plans the maps of arbitrary degree, integer circle powers, suspension
invariance, and the pole local-degree consequence on printed pages 136–137.
Two of its leaves are complete and twenty-nine remain unproved, bringing the
selected DAG to 299 formalizable leaves.

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
