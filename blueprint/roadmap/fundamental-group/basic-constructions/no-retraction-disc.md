---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Disc.not_exists_retraction
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

Formalized in `Hatcher/Disc/NoRetraction.lean` as
`Hatcher.Disc.not_exists_retraction`, with `D²` taken as
`Metric.closedBall (0 : ℂ) 1` and the boundary inclusion as
`Hatcher.Disc.incl`.

The Lean proof does not go through induced homomorphisms. The pinned Mathlib
has `FundamentalGroup.map` but no functoriality lemmas for it, so `π₁(r) ∘
π₁(i) = id` is not available off the shelf. Running the argument directly on
path classes is shorter: the boundary loop becomes nullhomotopic once pushed
into the disc, because the disc is convex and hence contractible, and pushing
that nullhomotopy back down through the retraction would make `ω`
nullhomotopic in `S¹`, contradicting winding number one.

## Depends on

- [The fundamental group of the circle](fundamental-group-circle.md)

## Sources

- [Hatcher §1.1, within the proof of Theorem 1.9, page 31](../../../sources/hatcher-1-1.md)
