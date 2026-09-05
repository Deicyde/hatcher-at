---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.IndexedConeAttachment.isOpenCover_lower_upper
---

# An indexed family of cones has a two-set open cover

For attaching maps `f j : S j → X`, construct the quotient of `X` with one
cone on each `S j`. Each index has its own apex, so different cells do not
acquire an artificial common center. When the index type is empty, the
construction is homeomorphic to `X` with no extra point.

The base with all positive-height cone points and the family of apex
neighborhoods with all subunit-height points are open and cover the quotient.
This is formalized by
`Hatcher.VanKampen.IndexedConeAttachment.isOpenCover_lower_upper`; the empty
case is `Hatcher.VanKampen.IndexedConeAttachment.emptyIndexHomeomorph`.

The upper member is generally a disjoint union of truncated cones, hence need
not be connected or contractible. Hatcher's auxiliary cover must still connect
these pieces before the binary van Kampen theorem applies.

## Depends on

- [A single cone attachment has a two-set open cover](single-cone-open-cover.md)

## Sources

- [Hatcher §1.2, construction used in Proposition 1.26 on pages 49–51](../../../../sources/hatcher-1-2.md)
