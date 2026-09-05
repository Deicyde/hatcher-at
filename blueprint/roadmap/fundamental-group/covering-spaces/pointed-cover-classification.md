---
article_id: af_238d1dd83722c5a2266b57e6
source_units: [hatcher-1-3-selected-spine]
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.BasedConnectedCover.classificationEquiv
---

# Pointed connected covers are classified by subgroups

**Hatcher, Theorem 1.38, based clause (page 67).** For a path-connected,
locally path-connected, semilocally simply-connected `X`, assigning the image
subgroup to a pointed connected cover gives a bijection from
basepoint-preserving isomorphism classes of covers to subgroups of
`π₁(X,x₀)`.

Intended artifact: `Hatcher.BasedConnectedCover.classificationEquiv`.

Formalized in `Hatcher/Covering/PointedCoverClassification.lean`. The
classification uses the quotient of pointed connected covers whose total
spaces live in the same universe as `X`. This fixed-universe quotient is
equivalent to the subgroups of `π₁(X,x₀)`. A separate cross-universe theorem,
`Hatcher.BasedConnectedCover.isomorphic_ofSubgroup_fundamentalGroupRange`,
shows that every pointed connected cover in any universe is isomorphic to its
canonical subgroup-cover representative in the fixed universe.

## Depends on

- [Pointed connected covering spaces](based-connected-cover.md)
- [Semilocally simply-connected spaces](universal-cover/semilocally-simply-connected.md)

## Proof depends on

- [The covering space associated to a subgroup](subgroup-cover-space.md)
- [The subgroup cover realizes the chosen subgroup](subgroup-cover-image.md)
- [Equal image subgroups characterize pointed cover isomorphism](pointed-cover-rigidity.md)

## Sources

- [Hatcher §1.3, Theorem 1.38, based clause](../../../sources/hatcher-1-3.md)
