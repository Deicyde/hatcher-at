---
declaration: proposition
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.SubgroupCover.range_map_eq
---

# The subgroup cover realizes the chosen subgroup

**Hatcher, Proposition 1.36 (pages 66–67).** Let `X` be path-connected,
locally path-connected, and semilocally simply-connected. For every subgroup
`H ≤ π₁(X,x₀)`, the pointed projection from `SubgroupCover H` has induced
fundamental-group image exactly `H`.

Intended artifact: `Hatcher.SubgroupCover.range_map_eq`.

A loop in `X` lifts from the constant-path class to the class represented by
that loop, and this endpoint is the basepoint of the quotient precisely when
the loop class belongs to `H`.

Formalized in `Hatcher/Covering/SubgroupCoverImage.lean`. The proof computes
the monodromy endpoint using the initial-segment lift and reduces equality with
the quotient basepoint to the defining subgroup relation.

## Depends on

- [The covering space associated to a subgroup](subgroup-cover-space.md)

## Proof depends on

- [The subgroup projection is a path-connected covering](subgroup-cover-is-covering.md)
- [The induced subgroup consists of loops with closed lifts](closed-lift-image.md)

## Sources

- [Hatcher §1.3, Proposition 1.36](../../../sources/hatcher-1-3.md)
