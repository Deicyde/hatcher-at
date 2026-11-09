---
article_id: af_018beb3e9d962f2092677b89
---

# Algebraic Topology (Hatcher) roadmap

Formalize selected results from Hatcher's *Algebraic Topology* in Lean 4 on
Mathlib, working outward from the fundamental group. Chapters follow the
book's order; fine leaves expose the actual source objects and maps.

The completed scope contains 299 formalizable leaves: 281 proved
locally and 18 supplied by pinned Mathlib. It includes the selected
fundamental-group spines, homology and excision applications, degree
foundations, and all twenty local-degree leaves through Proposition 2.30.
The completed thirty-one-leaf
[degree-realization and suspension milestone](homology/computations-and-applications/degree-realization-suspension/README.md)
constructs maps of arbitrary integer degree, calculates integer circle powers,
proves suspension invariance, and realizes arbitrary local degrees at both
suspension poles on printed pages 136–137.

The next [cellular-homology milestone](homology/computations-and-applications/cellular-homology/README.md)
adds fifteen planned leaves through Lemma 2.34 and Theorem 2.35 on printed
pages 137–140. The selected DAG therefore has 314 formalizable leaves,
with the previous 299 completed.

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
