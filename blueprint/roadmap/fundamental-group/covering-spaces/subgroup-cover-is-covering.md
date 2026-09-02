---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.SubgroupCover.isCoveringMap_proj
---

# The subgroup projection is a path-connected covering

Let `X` be path-connected, locally path-connected, and semilocally
simply-connected. For every `H ≤ π₁(X,x₀)`, the endpoint projection from
`SubgroupCover H` to `X` is a covering map and its total space is
path-connected.

The main artifact is `Hatcher.SubgroupCover.isCoveringMap_proj`; the same file
should provide `Hatcher.SubgroupCover.pathConnectedSpace`.

Use the images of Hatcher's basic sets `U[γ]`. If any points from two such sets
are identified by the subgroup relation, the whole sets are identified, so
their images are sheets over `U`.

Formalized in `Hatcher/Covering/SubgroupCoverIsCovering.lean`. The proof descends
the universal-cover basic opens through the subgroup quotient, proves that they
form disjoint sheets with discrete fibers, and builds the covering trivialization.

## Depends on

- [The covering space associated to a subgroup](subgroup-cover-space.md)

## Proof depends on

- [The endpoint map is a covering](universal-cover/universal-cover-is-covering.md)
- [The path-class cover is path-connected](universal-cover/universal-cover-path-connected.md)
- [The universal-cover basic sets form a basis](universal-cover/universal-cover-basis.md)

## Sources

- [Hatcher §1.3, proof of Proposition 1.36 on pages 66–67](../../../sources/hatcher-1-3.md)
