---
declaration: theorem
origin: cited
mathlib: true
mathlib_declaration: simply_connected_iff_unique_homotopic
mathlib_file: Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean
---

# Simply connected spaces have unique path-homotopy classes

**Hatcher, Proposition 1.6 (page 28).** A space is simply connected if and
only if every pair of points is joined by a unique path-homotopy class.

This is exactly the pinned theorem `simply_connected_iff_unique_homotopic`:

`SimplyConnectedSpace X ↔ Nonempty X ∧
  ∀ x y : X, Nonempty (Unique (Path.Homotopic.Quotient x y))`.

The explicit `Nonempty X` conjunct prevents the uniqueness condition from
holding vacuously. Mathlib also provides
`simply_connected_iff_paths_homotopic'`, the equivalent formulation with an
explicit `PathConnectedSpace X` hypothesis and a proof that every two paths
with common endpoints are homotopic.

## Depends on

- [Path homotopy is an equivalence relation](path-homotopy-equivalence.md)

## Sources

- [Hatcher §1.1, Proposition 1.6, page 28](../../../sources/hatcher-1-1.md)
