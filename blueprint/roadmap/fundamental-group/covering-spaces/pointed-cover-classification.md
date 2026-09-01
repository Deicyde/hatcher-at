---
declaration: theorem
origin: cited
not_ready: true
---

# Pointed connected covers are classified by subgroups

**Hatcher, Theorem 1.38, based clause (page 67).** For a path-connected,
locally path-connected, semilocally simply-connected `X`, assigning the image
subgroup to a pointed connected cover gives a bijection from
basepoint-preserving isomorphism classes of covers to subgroups of
`π₁(X,x₀)`.

Intended artifact: `Hatcher.BasedConnectedCover.classificationEquiv`.

The mathematical surjectivity and injectivity are already separate roadmap
nodes. This packaging node remains not ready until the project fixes the exact
quotient of the universe-indexed cover record by covering isomorphism, or an
equivalent small skeleton. The theorem must not quantify over an unbounded
universe and call the result a set.

## Depends on

- [Pointed connected covering spaces](based-connected-cover.md)
- [Semilocally simply-connected spaces](universal-cover/semilocally-simply-connected.md)

## Proof depends on

- [The covering space associated to a subgroup](subgroup-cover-space.md)
- [The subgroup cover realizes the chosen subgroup](subgroup-cover-image.md)
- [Equal image subgroups characterize pointed cover isomorphism](pointed-cover-rigidity.md)

## Sources

- [Hatcher §1.3, Theorem 1.38, based clause](../../../sources/hatcher-1-3.md)
