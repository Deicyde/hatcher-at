# Algebraic Topology (Hatcher)

A Lean 4 formalization of selected results from Allen Hatcher's *Algebraic
Topology* (Cambridge University Press, 2002), built on Mathlib. Source notes
cite the official book without redistributing its text.

Every main-line chapter and numbered section is mapped. The selected roadmap
contains 314 formalizable leaves: 299 are complete (281 proved locally and
18 supplied by exact pinned Mathlib declarations), and 15 are planned. The twenty-leaf
[local-degree milestone](roadmap/homology/computations-and-applications/local-degree/README.md)
is complete through Proposition 2.30, including the geometric finite-puncture
coproduct, projection matrix, orientation sum, and the empty finite fiber.

The completed [degree-realization and suspension milestone](roadmap/homology/computations-and-applications/degree-realization-suspension/README.md)
covers the actual pinch-and-fold construction, integer circle powers,
Proposition 2.33's natural cone-boundary comparison, and arbitrary local
integer degrees in sphere dimension at least two. Its germ-invariance and
singleton-fiber comparisons, geometric constructions and degree consequences
are formalized; all thirty-one leaves are complete. The new
[cellular-homology milestone](roadmap/homology/computations-and-applications/cellular-homology/README.md)
plans Lemma 2.34, the cellular complex and Theorem 2.35 in fifteen leaves.
Thirteen residual source areas remain queued, not excluded or claimed
externally blocked.

- [Roadmap](roadmap/README.md) — the mathematical book and its dependencies.
- [Coverage](coverage/README.md) — the source boundary, dispositions, and fine
  roadmap links.
- [Sources](sources/README.md) — exact citations and project specifications.
