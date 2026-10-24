# Hatcher §2.2, Local degree and Proposition 2.30

Selected material from Hatcher, *Algebraic Topology*, §2.2, beginning at the
bottom of printed page 135 and ending with Proposition 2.30 on printed page
136 (PDF pages 144–145). The repository-local official PDF has SHA-256
`bebb3032bf9021b956da3bd070eb6c67dc662cf849be9cdf6679f677560e5618`.
Statements below are paraphrased; consult the official PDF for the source text
and diagram.

## Local degree

Let `n > 0`, let `f : Sⁿ → Sⁿ`, and suppose a point `y : Sⁿ` has finite
fiber `f⁻¹(y) = {x₁, …, xₘ}`. Hatcher chooses pairwise disjoint
neighborhoods `Uᵢ` of the fiber points that map into a neighborhood `V` of
`y`. Excision and the long exact sequence of a pair identify

`Hₙ(Uᵢ, Uᵢ - {xᵢ}; ℤ)` and `Hₙ(V, V - {y}; ℤ)`

with the oriented group `Hₙ(Sⁿ; ℤ) ≅ ℤ`. Under these identifications, the
map induced by `f` is multiplication by an integer. This integer is the local
degree of `f` at `xᵢ`, written `deg(f|xᵢ)`.

The formalization uses the equivalent punctured-pair description

`(Uᵢ, Uᵢ - {xᵢ}) → (Sⁿ, Sⁿ - {y})`.

The target neighborhood `V` is therefore not retained as auxiliary data:
including `(V,V-{y})` into the punctured sphere pair is an excision
isomorphism, and composing with it gives the same local integer. An isolated
preimage neighborhood is any open `U` containing `x` such that
`f(z) = y` for `z ∈ U` implies `z = x`. The roadmap proves that shrinking
such a neighborhood does not change the integer, then defines local degree
from the resulting neighborhood-independent value. This arbitrary
isolated-preimage API and its explicit independence theorem are a
project-authored generalization of Hatcher's finite-fiber construction.

For a homeomorphism there is one preimage point and all comparison maps are
isomorphisms. Its local degree agrees with its global degree and is therefore
`1` or `-1`. More generally, if the restriction on a chosen neighborhood is a
homeomorphism onto a neighborhood of `y`, all local comparison maps are
isomorphisms and the local degree is `1` or `-1`.

## Proposition 2.30

For the finite fiber above, Hatcher proves

`deg f = ∑ x ∈ f⁻¹(y), deg(f|x)`.

Excision identifies

`Hₙ(Sⁿ, Sⁿ - f⁻¹(y); ℤ)`

with the direct sum of the local groups
`Hₙ(Uᵢ, Uᵢ - {xᵢ}; ℤ)`. The inclusion of the `i`th local group is the `i`th
summand injection. Projection to the pair punctured only at `xᵢ` kills every
other summand, while the global sphere class maps to the tuple whose every
component is the positively oriented local class. Thus the finite-puncture
class is the sum of the local classes. Applying the pair map induced by `f`
sends each summand to its local-degree multiple of the target local class.
Naturality with the ordinary sphere class identifies the same composite with
multiplication by `deg f`, yielding the formula.

## Selected boundary

This source unit includes the definition of local degree at an isolated
preimage, its independence of the chosen neighborhood, the homeomorphism
example, and Proposition 2.30 for a finite fiber of a map of
positive-dimensional spheres.

The theorem also permits an empty finite fiber. Hatcher does not discuss this
case explicitly; it is a deliberate strengthening that recovers the completed
nonsurjective-degree-zero theorem.

It stops immediately before Example 2.31. The separate
[degree-realization and suspension unit](hatcher-2-2-degree-applications.md)
now decomposes Examples 2.31–2.32, Proposition 2.33, and the pole observation.
Cellular homology, the Hopf converse, and Theorem 2.27 remain queued.

## Existing prerequisites and pinned-library boundary

The completed project supplies integral sphere orientation and degree, relative
homology, excision, local-homology invariance under restriction to an open
neighborhood, and the canonical relative-chain and relative-homology comparisons
for coproducts of arbitrary topological pairs. The pointed constructions remain
exact compatibility specializations. Local degree at an isolated preimage,
neighborhood independence, its homeomorphism calculation, finite disjoint
neighborhoods, and the corresponding pair maps are also formalized locally.
The completed roadmap constructs the finite-puncture homology coproduct,
geometric projection matrix, and orientation sum, then proves Proposition
2.30 for every finite fiber, including the empty one. All twenty leaves of
this source unit are formalized locally.

Mathlib `v4.34.1`, pinned at
`d13f23b723b8a846827a245b89c10fc7d3f11612`, supplies finite Hausdorff
separation through `Set.Finite.t2_separation`, categorical finite sums, and the
topological sigma type. The project contains the local-degree definition, its
comparison laws, and Proposition 2.30. Neither local degree nor Proposition
2.30 is supplied by pinned Mathlib. No leaf in this source unit is marked
`mathlib: true`.
