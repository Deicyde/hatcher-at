---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Disc.not_exists_retraction
---

# The circle is not a retract of the disc

There is no continuous `r : D² → S¹` restricting to the identity on `S¹`.

Hatcher's proof is direct. A nontrivial loop in `S¹` becomes nullhomotopic
after inclusion into the convex disc. Composing that nullhomotopy with a
putative retraction would make the original loop nullhomotopic in `S¹`, a
contradiction.

Hatcher gives this argument inside the proof of Theorem 1.9 on page 32 rather
than as a numbered result, so its origin is `bridged`. Proposition 1.17 on
page 36 later repackages the same obstruction using the injectivity of the
homomorphism induced by a retract. This node keeps the earlier path-level
argument because it is the route Hatcher actually uses for Brouwer.

Mathlib has convexity of the disc and contractibility of convex sets, so
`π₁(D²) = 0` is available and does not need its own node.

Formalized in `Hatcher/Disc/NoRetraction.lean` as
`Hatcher.Disc.not_exists_retraction`, with `D²` taken as
`Metric.closedBall (0 : ℂ) 1` and the boundary inclusion as
`Hatcher.Disc.incl`.

The Lean proof follows Hatcher's direct route on path classes: the boundary
loop becomes nullhomotopic once pushed into the disc, and applying the
retraction to that homotopy would make the winding-one loop nullhomotopic in
`S¹`.

## Proof depends on

- [The fundamental group of the circle](fundamental-group-circle.md)

## Sources

- [Hatcher §1.1, within the proof of Theorem 1.9, page 32](../../../sources/hatcher-1-1.md)
