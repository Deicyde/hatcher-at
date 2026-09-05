---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.PointedWedge.exists_vanKampenCover
---

# The standard cover of a well-pointed wedge

Define `Hatcher.WellPointedAt x₀` to mean that `x₀` lies in an open subset
`N` equipped with a contraction to `x₀` that fixes `x₀` throughout. Express
the contraction on the subtype `N` using `ContinuousMap.HomotopyRel`, relative
to the singleton containing the chosen basepoint. This is the formal version
of Hatcher's hypothesis that the basepoint is a deformation retract of an open
neighborhood.

For a nonempty family of path-connected spaces `X i` with well-pointed
basepoints `x₀ i`, construct the standard cover `W i` of
`Hatcher.PointedWedge X x₀`. If `q` is the quotient map and `N j` is the chosen
neighborhood in the `j`th summand, require

`q ⁻¹' W i = {none} ∪ {some ⟨j, x⟩ | j = i ∨ x ∈ N j}`.

Prove that every `W i` is open, all contain the wedge point, and their union is
the whole wedge. Each `W i` must deformation retract onto the image of `X i`,
with a basepoint-preserving homotopy equivalence compatible with the canonical
summand inclusion. For `i ≠ j`, prove that `W i ∩ W j` deformation retracts to
the wedge point. Deduce the member, pairwise-intersection, and
triple-intersection path-connectivity hypotheses required by van Kampen.

Intended artifact: `Hatcher.PointedWedge.exists_vanKampenCover`.

The same development should handle the empty-family boundary case separately by
showing that `Hatcher.PointedWedge X x₀` is a one-point, hence contractible,
space when the index type is empty. The cover theorem itself is scoped to a
nonempty index type, since an empty indexed family cannot cover the wedge
point.

This node owns the quotient-space elimination and continuity lemmas needed to
define the cover and its simultaneous deformation homotopies. The final wedge
fundamental-group theorem should consume this package rather than reconstruct
the point-set topology.

Formalized across `Hatcher/VanKampen/WellPointedWedgeCover.lean`,
`WellPointedWedgeNeckContraction.lean`, and
`WellPointedWedgeMemberDeformation.lean`.

## Depends on

- [The pointed wedge of a family of spaces](pointed-wedge.md)

## Sources

- [Hatcher §1.2, Example 1.21](../../../sources/hatcher-1-2.md)
