# The fundamental group

Hatcher's Chapter 1 (pages 21–96) builds the first algebraic invariant of a
space and the first real computations with it. Loops at a basepoint, taken up
to homotopy, form a group `π₁(X, x₀)`; a continuous map induces a homomorphism;
homotopy equivalences induce isomorphisms. The invariant only earns its keep
once something can be computed with it, and the chapter's three sections supply
in turn the seed computation, a general gluing tool, and the structural theory
that explains both.

[Basic constructions](basic-constructions/README.md) sets up `π₁` and computes
`π₁(S¹) ≅ ℤ` by lifting loops along `ℝ → S¹`. That one calculation immediately
yields the fundamental theorem of algebra, Brouwer's fixed point theorem for
the disc, and Borsuk–Ulam for `S²`.

[Van Kampen's theorem](van-kampen/README.md) computes `π₁` of a space glued
from pieces whose fundamental groups are known, as a free product of the pieces
amalgamated over their intersections. It turns the circle computation into
`π₁` of every graph, wedge, and two-dimensional cell complex.

[Covering spaces](covering-spaces/README.md) recasts both: subgroups of
`π₁(X)` correspond to covering spaces of `X`, and the loop-lifting argument
behind the circle computation becomes an instance of a general classification.

Mathlib has `FundamentalGroup`, `FundamentalGroupoid`, and the covering-space
lifting theorems including monodromy, but none of the three computations. This
chapter is where the project starts.

## Sections

- [Basic constructions](basic-constructions/README.md)
- [Van Kampen's theorem](van-kampen/README.md)
- [Covering spaces](covering-spaces/README.md)

## Sources

- [Hatcher, Chapter 1](../../sources/hatcher.md)
