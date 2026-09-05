---
article_id: af_4924ce7fc94298427e633deb
source_units: [hatcher-1-3-selected-spine]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.UniversalCover.simplyConnectedSpace
---

# The path-class cover is simply-connected

Let `X` be path-connected, locally path-connected, and semilocally
simply-connected. The total space `Hatcher.UniversalCover X x₀` is
simply-connected.

Intended artifact: `Hatcher.UniversalCover.simplyConnectedSpace`.

Follow Hatcher's proof. The endpoint projection injects fundamental groups,
and a base loop in the image has a closed lift in the path-class cover only
when its original homotopy class is trivial.

Formalized in `Hatcher/Covering/UniversalCoverSimplyConnected.lean`. The proof
identifies projected paths with their endpoint coordinates by lift uniqueness,
cancels a projected loop, and applies covering-map injectivity on path classes.

## Depends on

- [The path-class universal-cover space](universal-cover-path-space.md)

## Proof depends on

- [The endpoint map is a covering](universal-cover-is-covering.md)
- [The path-class cover is path-connected](universal-cover-path-connected.md)
- [Covering maps inject path-homotopy classes](../covering-injective-path-classes.md)
- [The induced subgroup consists of loops with closed lifts](../closed-lift-image.md)

## Sources

- [Hatcher §1.3, simple connectivity proof on page 65](../../../../sources/hatcher-1-3.md)
