# Algebraic Topology (Hatcher) roadmap

Formalize results from Hatcher's *Algebraic Topology* in Lean 4 on top of
Mathlib, working outward from the fundamental group.

Mathlib already carries much of the book's groundwork: path homotopy, the
fundamental groupoid, covering spaces with their lifting theorems, CW
complexes, and singular homology in degree zero. What it lacks is the book's
spine of computations, starting with `π₁(S¹) ≅ ℤ`. The roadmap therefore maps
the whole book but decomposes it from that point.

Chapters follow Hatcher's own order. The selected §1.1 slice is fully
formalized, and the selected §1.2 and §1.3 spines are decomposed into
formalization nodes. One Appendix prerequisite is isolated. The remaining
source is mapped so the book reads end to end and later work has somewhere to
land. The
[coverage contract](../coverage/README.md) says which is which, and
[the source notes](../sources/hatcher.md) fix the citation scheme.

## Chapters

- [Some underlying geometric notions](underlying-geometric-notions/README.md)
- [The fundamental group](fundamental-group/README.md)
- [Homology](homology/README.md)
- [Cohomology](cohomology/README.md)
- [Homotopy theory](homotopy-theory/README.md)
- [Appendix](appendix/README.md)
