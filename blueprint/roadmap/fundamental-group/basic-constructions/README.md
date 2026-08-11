# Basic constructions

Hatcher §1.1 (pages 25–38). This is the project's decomposed section.

Paths in a space `X` with fixed endpoints, taken up to homotopy, compose; loops
at a basepoint `x₀` therefore form a group `π₁(X, x₀)`, and a path between
basepoints induces an isomorphism between the groups it joins. Mathlib already
has all of this as `Path.Homotopic` and `FundamentalGroup`, so Propositions
1.2, 1.3, 1.5, and 1.6 are prior art rather than work, and the section's first
half contributes no nodes.

## The circle

The section's real content is the computation `π₁(S¹) ≅ ℤ`. Hatcher compares
loops in `S¹` with paths in `ℝ` along `p(s) = (cos 2πs, sin 2πs)`, and needs
only that this map is a covering.

- [The real line covers the circle](circle-covering.md)

Every loop then lifts to a path in `ℝ` starting at `0` and ending at an
integer, and that integer is unchanged by path homotopy because homotopies lift
too. Mathlib supplies both lifting facts as `IsCoveringMap.liftPath` and
`IsCoveringMap.liftHomotopy` with `monodromy_theorem`, so the invariant can be
defined directly.

- [Winding number of a loop in the circle](winding-number.md)

The loop `ωₙ(s) = (cos 2πns, sin 2πns)` realizes each integer, and comparing an
arbitrary lift with the linear path `s ↦ ns` shows the winding number is
faithful. That is the theorem.

- [The fundamental group of the circle](fundamental-group-circle.md)

## Consequences

Three classical theorems follow, all from the observation that a retraction
`D² → S¹` would factor the identity of `ℤ` through the trivial group.

- [The circle is not a retract of the disc](no-retraction-disc.md)
- [Brouwer's fixed point theorem for the disc](brouwer-disc.md)

The same nonvanishing of winding number, applied to the loops traced by a
polynomial on circles of growing radius, gives a topological proof of a result
Mathlib already knows by other means.

- [The fundamental theorem of algebra](fundamental-theorem-algebra.md)

## Induced homomorphisms

The closing part of the section turns to maps between spaces. Its one result
this project needs is that higher spheres are simply connected, which rests on
a subdivision lemma that §1.2 will later generalize into van Kampen.

- [A loop splits across an open cover](loop-in-open-cover.md)
- [Higher spheres are simply connected](sphere-simply-connected.md)

Borsuk–Ulam combines both halves of the section: the equator of `S²` bounds a
disc, so an odd map `S² → S¹` restricted to it is simultaneously nullhomotopic
and of odd winding number.

- [Borsuk–Ulam for the two-sphere](borsuk-ulam-sphere.md)

Corollary 1.11 and Corollary 1.16 close Hatcher's section and are deliberately
out of this slice; see the [coverage contract](../../../coverage/README.md).

## Sources

- [Hatcher §1.1](../../../sources/hatcher-1-1.md)
