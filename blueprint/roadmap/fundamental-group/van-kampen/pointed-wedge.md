---
declaration: def
origin: background
---

# The pointed wedge of a family of spaces

Define the wedge of an arbitrary family of pointed spaces as the quotient of
`Option (Σ i, X i)` by the smallest equivalence relation identifying `none`
with every `some ⟨i, x₀ i⟩`, with the quotient topology and the class of `none`
as basepoint. Supply the inclusions of each summand and their continuity
lemmas. This convention makes the wedge of an empty family a one-point space.

Intended artifact: `Hatcher.PointedWedge`.

This project-authored representation follows Hatcher's Chapter 0 definition.
Mathlib has no topological wedge construction in the pinned revision.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2, Example 1.21 and the adopted wedge representation](../../../sources/hatcher-1-2.md)
