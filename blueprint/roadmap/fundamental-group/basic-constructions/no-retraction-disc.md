---
declaration: theorem
origin: bridged
---

# The circle is not a retract of the disc

There is no continuous `r : D² → S¹` restricting to the identity on `S¹`.

Suppose one existed, and let `i : S¹ → D²` be the inclusion. Then `r ∘ i = id`,
so applying `π₁` gives `r∗ ∘ i∗ = id` on `π₁(S¹) ≅ ℤ`. But that factors the
identity of `ℤ` through `π₁(D²)`, which is trivial because `D²` is convex.
An identity map cannot factor through the trivial group when the group is
nontrivial, so no retraction exists.

Hatcher states this inside the proof of Theorem 1.9 (page 31) rather than as a
numbered result, so its origin is `bridged`. It is worth its own node because
both Brouwer and later dimension-raising arguments reuse it, and because it is
the whole content of the deduction: Theorem 1.9 is a short corollary.

Mathlib has convexity of the disc and contractibility of convex sets, so
`π₁(D²) = 0` is available and does not need its own node.

Intended artifact: `Hatcher.Disc.not_isRetract_circle` in
`Hatcher/Disc/NoRetraction.lean`.

## Depends on

- [The fundamental group of the circle](fundamental-group-circle.md)

## Sources

- [Hatcher §1.1, within the proof of Theorem 1.9, page 31](../../../sources/hatcher-1-1.md)
