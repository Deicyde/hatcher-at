# Hatcher §2.2, Degree foundations

Selected material from Hatcher, *Algebraic Topology*, §2.2, printed pages
134–135 (PDF pages 143–144). The repository-local official PDF has SHA-256
`bebb3032bf9021b956da3bd070eb6c67dc662cf849be9cdf6679f677560e5618`.
Statements below are paraphrased; consult the official PDF for the source text.

## Degree and its formal properties

For `n > 0`, Hatcher defines the degree of a continuous map
`f : Sⁿ → Sⁿ` as the integer by which the induced endomorphism of the
infinite cyclic group `Hₙ(Sⁿ;ℤ)` multiplies a chosen generator. Printed page
134 records these properties:

- the identity has degree `1`;
- a nonsurjective map has degree `0`, by factoring through a punctured,
  contractible sphere;
- homotopic maps have equal degree;
- degree is multiplicative under composition, so a homotopy equivalence has
  degree `1` or `-1`;
- a reflection interchanging two hemispheres has degree `-1`, computed on the
  ordered two-simplex generator from Example 2.23;
- the antipodal map has degree `(-1)^(n+1)`, as a composite of coordinate
  reflections; and
- a fixed-point-free map is homotopic to the antipodal map by normalizing the
  straight-line homotopy from `f(x)` to `-x`.

Only the forward implication “homotopic maps have equal degree” belongs to
this slice. Hatcher explicitly postpones the converse to Corollary 4.25.

## Theorem 2.28

On printed page 135, Hatcher proves that `Sⁿ` admits a continuous nowhere-zero
tangent vector field exactly when `n` is odd. A tangent field is treated as an
ambient vector field `v(x) ∈ ℝⁿ⁺¹` orthogonal to `x`.

After normalizing such a field, the formula
`(cos t)x + (sin t)v(x)` gives a homotopy from the identity to the antipodal
map and forces `n` to be odd by the degree calculation. Conversely, in odd
dimension the coordinates are paired and rotated by a quarter turn to give an
explicit unit tangent field.

## Proposition 2.29

Still on printed page 135, an action of a group `G` on `Sⁿ` determines a
degree homomorphism `G → {±1}`. If the action is free, every nonidentity
element is fixed-point-free. For even positive `n`, the preceding degree
formula makes this homomorphism injective, so a nontrivial acting group is
isomorphic to `ℤ/2`. The antipodal involution supplies the free `ℤ/2` action.

## Selected boundary

This source unit contains the degree definition and properties (a)–(g),
Theorem 2.28, and Proposition 2.29, and stops immediately before Hatcher
introduces local degree at the bottom of printed page 135.

Local degree, Proposition 2.30, Examples 2.31–2.32, suspension invariance in
Proposition 2.33, cellular homology, the Hopf converse, and Theorem 2.27 are
not part of this milestone.

## Existing prerequisites and pinned-library boundary

The completed Example 2.23 milestone supplies the ordered sphere class
`Hatcher.Simplex.doubleSimplexSphereFundamentalClass` and its generator
theorem. The completed reduced-homology API supplies the positive-degree
comparison with ordinary homology and homotopy invariance.

Mathlib `v4.34.1`, pinned at
`d13f23b723b8a846827a245b89c10fc7d3f11612`, supplies stereographic
projection, Euclidean sphere geometry, integer endomorphisms and units,
homotopies, and homeomorphism groups. It has no exact definition or theorem
for mapping degree, local degree, Theorem 2.28, or Proposition 2.29. No leaf
in this source unit is therefore marked `mathlib: true`.
