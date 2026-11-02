# Algebraic Topology (Hatcher)

A Lean 4 formalization of selected results from Allen Hatcher's *Algebraic
Topology* (Cambridge University Press, 2002), built on Mathlib. Source notes
cite the official book without redistributing its text.

Every main-line chapter and numbered section is mapped. The selected roadmap
contains 299 formalizable leaves: 252 are proved locally, 18 are exact pinned
Mathlib declarations, and 29 remain unproved. The twenty-leaf
[local-degree milestone](roadmap/homology/computations-and-applications/local-degree/README.md)
is complete through Proposition 2.30, including the geometric finite-puncture
coproduct, projection matrix, orientation sum, and the empty finite fiber.

The new [degree-realization and suspension milestone](roadmap/homology/computations-and-applications/degree-realization-suspension/README.md)
covers the actual pinch-and-fold construction, integer circle powers,
Proposition 2.33's natural cone-boundary comparison, and arbitrary local
integer degrees in sphere dimension at least two. Its germ-invariance and
singleton-fiber comparisons are formalized; twenty-nine of its thirty-one
leaves remain unproved. The thirteen remaining source areas are queued, not excluded or
claimed externally blocked.

- [Roadmap](roadmap/README.md) — the mathematical book and its dependencies.
- [Coverage](coverage/README.md) — the source boundary, dispositions, and fine
  roadmap links.
- [Sources](sources/README.md) — exact citations and project specifications.
