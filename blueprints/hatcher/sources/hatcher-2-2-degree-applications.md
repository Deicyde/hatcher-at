# Hatcher §2.2, Degree realization and suspension

Selected material from Hatcher, *Algebraic Topology*, beginning with Example
2.31 on printed page 136 and ending immediately before Cellular Homology on
printed page 137 (PDF pages 145–146). The official source PDF has SHA-256
`bebb3032bf9021b956da3bd070eb6c67dc662cf849be9cdf6679f677560e5618`.
Both pages and the Proposition 2.33 diagram were inspected directly in that
PDF. The following statements are paraphrases, not redistributed book text.

## Example 2.31

For every positive sphere dimension and every integer d, Hatcher constructs a
continuous sphere self-map of degree d. Collapse the complement of k disjoint
open balls to obtain a wedge of k spheres, then fold those spheres onto one
sphere. Away from the common collapsed point the fiber has one point in each
ball and the map is locally a homeomorphism there. Reflections on the summands
correct its local signs. Proposition 2.30 computes the global degree as their
sum, producing degree +k or −k; the constant map supplies degree zero.

The fine DAG retains this actual pinch-and-fold construction. It does not
replace the source witness by an unspecified map with a prescribed degree.
Compactification and quotient comparisons are project-authored geometric
bridges. The refined regular-locus statement concerns every target other than
the chosen collapsed point; sign correction uses the computed unit degrees,
not an extra positively-oriented-chart hypothesis.

## Example 2.32

On the complex unit circle, the integer power map z ↦ z^d has degree d. The
zero power is constant. Negative powers factor through inversion, which is a
reflection of degree −1. For a positive exponent k, every target has k roots
and the map is a local homeomorphism at each root.

Hatcher removes local positive angular stretching by a deformation to a
rotation. The rotation is homotopic to the identity, so each local degree is
+1. The finite-fiber degree formula then gives k. The roadmap makes the local
deformation explicit on a short arc and requires it to avoid the target away
from the center throughout; shrinking invariance for one fixed map alone does
not justify this deformation.

## Proposition 2.33

Suspending a sphere map preserves its degree. Hatcher uses the cone
CSⁿ = (Sⁿ × I)/(Sⁿ × {1}), with retained base at height zero, and identifies
CSⁿ/Sⁿ with Sⁿ⁺¹. The induced cone-base pair map has the suspension as its
quotient map. The natural connecting isomorphism

`H̃ₙ₊₁(Sⁿ⁺¹;ℤ) ≅ H̃ₙ(Sⁿ;ℤ)`

intertwines the two induced maps. It therefore preserves their signed integer
multipliers. The cone/base model and both suspension poles agree with the
particular sphere suspension described in Chapter 0, Operations on Spaces,
printed page 8 (PDF page 17).

In the project's existing retained cone the cylinder height r has apex at zero
and base at one. The change t = 1−r matches Hatcher's convention. The quotient
homeomorphism sends (x,r) to
`(sqrt(1−(2r−1)²) x, 2r−1)` in the next sphere, making the collapsed base the
north pole and the apex the south pole. These are proved geometry targets.
The natural reduced comparison includes n = 0, but the existing ordinary
degree is defined only for n > 0; ordinary H₀(S⁰) is not substituted for
reduced H₀(S⁰).

Iterating suspension on the circle powers is Hatcher's alternative construction
of the maps already asserted in Example 2.31. The roadmap reuses the degree
preservation theorem and circle-power calculation rather than adding a second
bare arbitrary-degree existence article.

## Pole fibers and local-degree realization

The unnumbered paragraph immediately following Proposition 2.33 observes that
each pole of a suspension has exactly that pole as its fiber. The degree-sum
formula therefore identifies the local degree there with the global degree,
without a local-homeomorphism assumption. Consequently every integer occurs
as a local degree for maps of Sᵐ when m ≥ 2. The explicit suspension witness
realizes the same integer at both poles.

A shared singleton-fiber lemma derives isolation and the local/global equality
from the completed Proposition 2.30. It is reused for ball-collapse maps and
suspension poles; no additional finite-fiber or isomorphism premise is assumed.

## Selected boundary and existing prerequisites

This unit contains Examples 2.31–2.32, Proposition 2.33, its iterated-suspension
consequence, and the entire pole/local-degree paragraph. It stops before the
Cellular Homology heading and Lemma 2.34. The remaining cellular and
Mayer–Vietoris applications and coefficients remain queued in the residual
§2.2 coverage row, not treated as external blockers or user exclusions.

The previous degree and twenty-leaf local-degree milestones are formalized
locally. Existing cone/disk geometry, pointed wedges, good-pair quotient
comparisons, relative-sequence naturality, and the reduced sphere computation
are reused. Pinned Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` supplies one-point compactification,
Euclidean ball and circle charts, circle powers and their finite coverings,
roots of unity, and closed-ball contractibility. No new endpoint here is
asserted as exact upstream Mathlib coverage.
