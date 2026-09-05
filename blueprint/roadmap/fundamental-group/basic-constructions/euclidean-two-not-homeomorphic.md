---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.not_nonempty_homeomorph_euclideanTwo
---

# Euclidean two-space is distinguished by dimension

**Hatcher, Corollary 1.16 (page 36).** Euclidean two-space is not
homeomorphic to Euclidean `n`-space when `n ≠ 2`.

Formalized as `Hatcher.not_nonempty_homeomorph_euclideanTwo` in
`Hatcher/Euclidean/Dimension.lean`. A hypothetical homeomorphism is translated
to fix the origin and then restricted to the punctured spaces. For dimensions
at least three, radial decomposition retracts the punctured spaces onto their
unit spheres; the two-dimensional sphere is a circle with nontrivial
fundamental group, while the higher sphere is simply connected. Dimension one
is separated by path connectedness of the punctured plane and the intermediate
value theorem on the punctured line. Dimension zero is a cardinality edge
case.

## Depends on

- [The fundamental group of the circle](fundamental-group-circle.md)
- [Higher spheres are simply connected](sphere-simply-connected.md)

## Sources

- [Hatcher §1.1, Corollary 1.16, page 36](../../../sources/hatcher-1-1.md)
