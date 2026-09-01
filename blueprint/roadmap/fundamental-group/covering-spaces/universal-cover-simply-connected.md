---
declaration: theorem
origin: cited
---

# The path-class cover is simply-connected

Let `X` be path-connected, locally path-connected, and semilocally
simply-connected. The total space `Hatcher.UniversalCover X x₀` is
simply-connected.

Intended artifact: `Hatcher.UniversalCover.simplyConnectedSpace`.

Follow Hatcher's proof. The endpoint projection injects fundamental groups,
and a base loop in the image has a closed lift in the path-class cover only
when its original homotopy class is trivial.

## Depends on

- [The path-class universal-cover space](universal-cover-path-space.md)

## Proof depends on

- [The endpoint map is a covering](universal-cover-is-covering.md)
- [The path-class cover is path-connected](universal-cover-path-connected.md)
- [Covering maps inject path-homotopy classes](covering-injective-path-classes.md)
- [The induced subgroup consists of loops with closed lifts](closed-lift-image.md)

## Sources

- [Hatcher §1.3, simple connectivity proof on page 65](../../../sources/hatcher-1-3.md)
