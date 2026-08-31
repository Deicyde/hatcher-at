# Basic constructions

Hatcher §1.1 (pages 25–38). This is the project's decomposed section.

Paths in a space `X` with fixed endpoints, taken up to homotopy, compose; loops
at a basepoint `x₀` therefore form a group `π₁(X, x₀)`, and a path between
basepoints induces an isomorphism between the groups it joins. Mathlib already
has all of this as `Path.Homotopic` and `FundamentalGroup`, so Propositions
1.2, 1.3, 1.5, and 1.6, together with the convexity examples around them, are
prior art rather than work, and the section's first half contributes no nodes.

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

Mathlib's product construction for fundamental groupoids, together with the
circle computation above, also supplies Proposition 1.12 and Example 1.13
without separate roadmap nodes.

## Consequences

The circle computation first rules out a retraction `D² → S¹`; Brouwer's
theorem is the direct consequence of that obstruction.

- [The circle is not a retract of the disc](no-retraction-disc.md)
- [Brouwer's fixed point theorem for the disc](brouwer-disc.md)

Separately, the nonvanishing of winding number applied to loops traced by a
polynomial on circles of growing radius gives a topological proof of a result
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

Corollaries 1.11 and 1.16, Propositions 1.17 and 1.18, and Lemma 1.19 lie
outside the selected nine-node slice. Mathlib already expresses the core of
Proposition 1.18 and Lemma 1.19 at the fundamental-groupoid level; source-facing
wrappers and the other deferred results belong to a later §1.1 completion
pass. See the [coverage contract](../../../coverage/README.md).

## Sources

- [Hatcher §1.1](../../../sources/hatcher-1-1.md)
