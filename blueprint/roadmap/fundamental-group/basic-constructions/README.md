---
article_id: af_1591bc37435c2335cf4649b7
---

# Basic constructions

Hatcher §1.1 (pages 25–38). This is the project's first completed section.
Its twenty-two explicit roadmap nodes comprise eighteen local formalizations
and four pinned Mathlib-backed nodes.

## Paths and homotopy

Paths in a space `X` with fixed endpoints, taken up to homotopy, compose; loops
at a basepoint `x₀` therefore form a group `π₁(X, x₀)`, and a path between
basepoints induces an isomorphism between the groups it joins. Each opening
result now has its own node, including the local wrappers needed to match
Hatcher's affine formula and path-concatenation convention.

- [Straight-line homotopy between paths](affine-path-homotopy.md)
- [Path homotopy is an equivalence relation](path-homotopy-equivalence.md)
- [Path concatenation gives the fundamental-group law](fundamental-group-law.md)
- [Convex sets have trivial fundamental group](convex-trivial-fundamental-group.md)
- [A path induces change of basepoint](change-of-basepoint.md)
- [Simply connected spaces have unique path-homotopy classes](simply-connected-unique-path-classes.md)

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
circle computation above, supplies Proposition 1.12 and Example 1.13.

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

The closing part of the section turns to maps between spaces. The product
formula immediately computes the torus. The higher-sphere calculation rests
on a subdivision lemma reused by §1.2 as the surjectivity step in van Kampen.

- [The fundamental group of a product](product-fundamental-group.md)
- [The fundamental group of the torus](torus-fundamental-group.md)
- [A loop splits across an open cover](loop-in-open-cover.md)
- [Higher spheres are simply connected](sphere-simply-connected.md)
- [Euclidean two-space is distinguished by dimension](euclidean-two-not-homeomorphic.md)

Borsuk–Ulam combines both halves of the section: the equator of `S²` bounds a
disc, so an odd map `S² → S¹` restricted to it is simultaneously nullhomotopic
and of odd winding number.

- [Borsuk–Ulam for the two-sphere](borsuk-ulam-sphere.md)
- [Three closed sets covering the sphere contain an antipodal pair](three-closed-sets-antipodal.md)

The section also records the fundamental group's invariance under homotopy
equivalence, beginning with the special case of retracts.

- [Retractions and deformation retracts on the fundamental group](retractions-fundamental-group.md)
- [A homotopy equivalence induces a fundamental-group isomorphism](homotopy-equivalence-fundamental-group.md)
- [Homotopic maps differ by basepoint change](homotopic-maps-fundamental-group.md)

These twenty-two explicit nodes cover the section's numbered results, named
examples, and the intermediate circle and no-retraction constructions used by
its proofs. See the [coverage contract](../../../coverage/README.md).

## Sources

- [Hatcher §1.1](../../../sources/hatcher-1-1.md)
