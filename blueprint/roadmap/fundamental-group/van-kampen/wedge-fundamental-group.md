---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.fundamentalGroupEquivPointedWedge
---

# The fundamental group of a wedge

**Hatcher, Example 1.21 (page 43).** For an arbitrary family of path-connected
pointed spaces whose basepoints are deformation retracts of open
neighborhoods, the inclusions of the summands induce an isomorphism from the
indexed free product of their fundamental groups to the fundamental group of
their wedge.

Intended artifact: `Hatcher.fundamentalGroupEquivPointedWedge`.

Do not restrict the family to a finite index type. The well-pointed hypothesis
is part of Hatcher's statement and makes the standard open cover of the wedge
available to van Kampen.

Formalized in `Hatcher/VanKampen/WedgeFundamentalGroup.lean`, including the
empty-family case and the canonical formula on each free-product factor.

## Depends on

- [The pointed wedge of a family of spaces](pointed-wedge.md)
- [The standard cover of a well-pointed wedge](well-pointed-wedge-cover.md)

## Proof depends on

- [Van Kampen's quotient isomorphism](van-kampen-quotient.md)

## Sources

- [Hatcher §1.2, Example 1.21](../../../sources/hatcher-1-2.md)
