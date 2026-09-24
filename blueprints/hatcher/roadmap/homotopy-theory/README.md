---
article_id: af_037caa30bf6a99390ba6eb23
---

# Homotopy theory

Hatcher's Chapter 4 (pages 337–518). Mapped, not yet decomposed.

The chapter returns to the homotopy groups `πₙ(X)` that Chapter 1 began, now
with homology available as a tool. The tension it works through is that `πₙ`
is the more natural invariant and the harder one: it has no excision, no
Mayer–Vietoris, and `πₙ(Sᵏ)` is unknown in general, yet Whitehead's theorem
says a map of CW complexes inducing isomorphisms on all `πₙ` is a homotopy
equivalence.

[Homotopy groups](homotopy-groups/README.md) gives the definitions, Whitehead's
theorem, and cellular and CW approximation.

[Elementary methods of calculation](elementary-methods/README.md) supplies what
computation there is: the Freudenthal suspension theorem, the Hurewicz theorem
relating the first nontrivial `πₙ` to `Hₙ`, fiber bundles and their long exact
sequence, and stable homotopy groups.

[Connections with cohomology](connections-with-cohomology/README.md) represents
cohomology by Eilenberg–MacLane spaces, develops fibrations, Postnikov towers,
and obstruction theory.

Mathlib defines `HomotopyGroup` in `Mathlib/Topology/Homotopy/HomotopyGroup.lean`
and has substantial model-category and simplicial-homotopy infrastructure in
`AlgebraicTopology/ModelCategory/` and `AlgebraicTopology/SimplicialSet/`, which
is a different and in places more modern route to this material than Hatcher's.
None of the chapter's named theorems is upstream.

## Sections

- [Homotopy groups](homotopy-groups/README.md)
- [Elementary methods of calculation](elementary-methods/README.md)
- [Connections with cohomology](connections-with-cohomology/README.md)

## Sources

- [Hatcher, Chapter 4](../../sources/hatcher.md)
