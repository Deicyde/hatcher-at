---
article_id: af_405673b01dde9b3f6c535593
not_ready: true
---

# Some underlying geometric notions

Hatcher's Chapter 0 (pages 1–20) fixes the geometric vocabulary the rest of the
book runs on: homotopy and homotopy type, cell complexes, the standard
operations on spaces, two criteria for recognizing homotopy equivalences, and
the homotopy extension property. It states few numbered theorems; its role is
to make deformation retraction, mapping cylinder, and CW structure precise
enough to compute with.

Most of this is already in Mathlib. `ContinuousMap.Homotopy`,
`ContinuousMap.HomotopyEquiv`, and `ContractibleSpace` live in
`Mathlib/Topology/Homotopy/`, and CW complexes in
`Mathlib/Topology/CWComplex/Classical/`. The chapter is mapped rather than
decomposed: the roadmap draws on it, and nodes elsewhere cite Mathlib's
existing definitions instead of restating them.

The homotopy extension property and the point-set facts about cell complexes
that later chapters lean on are gathered in the book's appendix, mapped as the
roadmap's final chapter.

## Sources

- [Hatcher, Chapter 0](../../sources/hatcher.md)
