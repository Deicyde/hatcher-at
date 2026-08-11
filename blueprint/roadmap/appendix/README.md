# Appendix

Hatcher's appendix (pages 519–539). Mapped, not yet decomposed.

The point-set facts the main text uses without proving: the topology of cell
complexes, including that CW complexes are normal, locally contractible, and
compactly generated; the compact-open topology and the exponential law
`Map(X × Y, Z) ≅ Map(X, Map(Y, Z))`; the homotopy extension property for CW
pairs; and simplicial CW structures.

Mathlib covers part of this already. `ContinuousMap.compactOpen` and the
currying results are in `Mathlib/Topology/CompactOpen.lean`, and
`LocallyContractibleSpace` is in `Mathlib/Topology/Homotopy/LocallyContractible.lean`.
The CW-specific separation and homotopy-extension facts are not.

This chapter is mapped so that prerequisites discovered while decomposing the
main chapters have a home rather than being invented inline.

## Sources

- [Hatcher, Appendix](../../sources/hatcher.md)
