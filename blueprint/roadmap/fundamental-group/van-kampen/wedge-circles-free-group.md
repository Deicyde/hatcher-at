---
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.fundamentalGroupEquivWedgeCircles
---

# The fundamental group of a wedge of circles

For an arbitrary index type `ι`, the fundamental group of the pointed wedge
of `ι` copies of the circle is the free group on `ι`:

`π₁(∨ᵢ S¹) ≃* FreeGroup ι`.

The equivalence is formalized as
`Hatcher.fundamentalGroupEquivWedgeCircles`. It specializes Hatcher's
well-pointed wedge calculation, uses the winding-number equivalence for each
circle, and identifies the resulting indexed coproduct of infinite cyclic
groups with `FreeGroup ι`.

The companion theorem
`Hatcher.fundamentalGroupEquivWedgeCircles_inclusion_loopOfInt` checks the
generators: the winding-`n` loop included from the `i`th circle maps to
`FreeGroup.of i ^ n`.

## Depends on

- [The fundamental group of a wedge](wedge-fundamental-group.md)
- [The circle is well-pointed at one](cell-attachment-support/circle-well-pointed.md)
- [The fundamental group of the circle](../basic-constructions/fundamental-group-circle.md)

## Sources

- [Hatcher §1.2, Example 1.21 and the proof of Corollary 1.28](../../../sources/hatcher-1-2.md)
