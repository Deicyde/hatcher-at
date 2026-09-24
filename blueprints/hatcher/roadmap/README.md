---
article_id: af_018beb3e9d962f2092677b89
---

# Algebraic Topology (Hatcher) roadmap

Formalize results from Hatcher's *Algebraic Topology* in Lean 4 on top of
Mathlib, working outward from the fundamental group.

Mathlib already carries much of the book's groundwork: path homotopy, the
fundamental groupoid, covering spaces with their lifting theorems, CW
complexes, and singular homology in degree zero. What it lacks is the book's
spine of computations, starting with `π₁(S¹) ≅ ℤ`. The roadmap therefore maps
the whole book but decomposes it from that point.

Chapters follow Hatcher's own order. The 133 leaves in the pre-existing
selected §1.1, §1.2, §1.3, §2.1, and Appendix A.1 slices are complete: 119
local declarations and 14 pinned Mathlib declarations. The §1.3 spine extends
through Proposition 1.40. A second fifteen-leaf §2.1 slice now decomposes
reduced and relative homology, long exact sequences, naturality, and relative
homotopy invariance; its simplicial-pair foundation is gated on a Mathlib pin
update and the new branch is not claimed complete. The remaining source is
mapped for navigation and explicitly deferred so the book reads end to end
and later work has somewhere to land. The
[coverage contract](../coverage/README.md) says which is which, and
[the source notes](../sources/hatcher.md) fix the citation scheme.

## Chapters

- [Some underlying geometric notions](underlying-geometric-notions/README.md)
- [The fundamental group](fundamental-group/README.md)
- [Homology](homology/README.md)
- [Cohomology](cohomology/README.md)
- [Homotopy theory](homotopy-theory/README.md)
- [Appendix](appendix/README.md)
