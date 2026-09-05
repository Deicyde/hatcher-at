---
article_id: af_a1c43352820c5831e110d751
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: background
statement: formalized
proof: formalized
lean: Hatcher.PointedWedge
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

Formalized in `Hatcher/VanKampen/PointedWedge.lean`. The file also exports the
common basepoint, the canonical summand inclusions, their continuity, and the
basepoint-identification simp lemma.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2, Example 1.21 and the adopted wedge representation](../../../sources/hatcher-1-2.md)
