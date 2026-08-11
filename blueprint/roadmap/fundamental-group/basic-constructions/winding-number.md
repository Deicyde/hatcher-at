---
declaration: def
origin: bridged
---

# Winding number of a loop in the circle

Given a loop `f` in `S¹` based at `1`, lift it to the unique path `f̃` in `ℝ`
starting at `0`. Since `p(f̃(1)) = f(1) = 1`, the endpoint `f̃(1)` is an integer.
That integer is the winding number of `f`.

It is well defined on homotopy classes: a path homotopy between loops lifts to
a path homotopy between their lifts, and the endpoint of a path homotopy is
constant, so homotopic loops have equal winding numbers. Mathlib supplies both
halves — `IsCoveringMap.liftPath` with its uniqueness, and
`IsCoveringMap.liftHomotopy` together with `monodromy_theorem` — so this node
is the descent of the endpoint map to `π₁`, not a lifting argument from
scratch.

The result is a group homomorphism `π₁(S¹, 1) →* Multiplicative ℤ`, or
equivalently an additive map after unfolding `π₁`; the exact Lean spelling is
part of this node. Hatcher works with the uniqueness of `n` rather than naming
a map, so this construction is `bridged`.

Intended artifact: `Hatcher.Circle.windingNumber` in
`Hatcher/Circle/WindingNumber.lean`.

## Depends on

- [The real line covers the circle](circle-covering.md)

## Sources

- [Hatcher §1.1, Theorem 1.7, page 29](../../../sources/hatcher-1-1.md)
