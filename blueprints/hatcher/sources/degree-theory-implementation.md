# Degree-foundations implementation specification

This is a project-authored implementation specification for the selected
degree material on Hatcher §2.2, printed pages 134–135. It is not an
independent mathematical source. The cited statements and proof sketches are
recorded in the [degree source note](hatcher-2-2-degree.md).

## Mathematical scope

Formalize, for positive-dimensional standard spheres:

- Hatcher's integral degree and properties (a)–(g);
- Theorem 2.28, existence of a nowhere-zero tangent field exactly in odd
  dimension; and
- Proposition 2.29, classification of nontrivial groups acting freely on an
  even-dimensional sphere.

Stop before local degree. Do not add Proposition 2.30, Examples 2.31–2.32,
Proposition 2.33, cellular homology, the Hopf converse, or Theorem 2.27.

## Oriented integral sphere homology

Work at universe zero with `TopCat.sphere n`. Transport the completed ordered
double-simplex class through
`Hatcher.Reduced.homologyIsoOfPositiveDegree` to obtain an ordinary integral
homology generator in degree `n`, under `0 < n`. This fixes the orientation;
an arbitrary inhabitant of Hatcher's earlier unoriented sphere-homology
isomorphism is not sufficient.

Define the degree of `f : TopCat.sphere n ⟶ TopCat.sphere n` by conjugating
the induced ordinary-homology endomorphism through this oriented isomorphism
and evaluating the resulting endomorphism of `ℤ` at `1`. Record the equivalent
fundamental-class equation and the `AddCommGrpCat.asHom` characterization.

The source-facing API keeps Hatcher's hypothesis `0 < n`. It does not silently
extend the definition to `S⁰` by switching theories.

## Formal degree calculus

Prove identity, composition, and homotopy invariance from functoriality and
the completed homotopy-invariance API. A self-homotopy-equivalence has degree
a unit of `ℤ`, hence `1` or `-1`. Package the degree of a sphere
homeomorphism as a multiplicative character into `ℤˣ` for later group actions.

For a nonsurjective map, choose a missed point and factor through its
complement. Publish the stereographic homeomorphism from a punctured sphere
to Euclidean space and the resulting contractibility instance; use reduced
homology vanishing to prove that the induced top-dimensional map, hence the
degree, is zero.

## Reflections and the antipodal map

Define an automorphism of the ordered double-simplex pushout that exchanges
its two summands. Prove at chain and homology level that it negates the
first-simplex-minus-second-simplex class.

Define coordinate sign-change homeomorphisms of `TopCat.sphere n`. Show that
the last-coordinate reflection corresponds, under
`Hatcher.Simplex.doubleSimplexIsoSphere`, to the double-simplex swap. Deduce
that its degree is `-1`, then use orthogonal conjugacy to prove the same theorem
for reflection across the equator normal to any unit vector. Record coordinate
reflections as special cases and compute the antipodal degree by factoring it
into all `n+1` coordinate reflections. This route is the source's Example 2.23
computation and does not use Theorem 2.27.

For a fixed-point-free map, prove the normalized expression
`((1-t)f(x)-tx)/‖(1-t)f(x)-tx‖` is defined and continuous and gives a homotopy
to the antipodal map. Homotopy invariance then gives property (g).

## Tangent fields

Represent a tangent vector field as a continuous ambient map
`v : Sⁿ → ℝⁿ⁺¹` with `⟪x,v(x)⟫ = 0`. Its nonvanishing predicate is pointwise
inequality with zero. Normalize a nonvanishing field and construct Hatcher's
cosine–sine homotopy from the identity to the antipodal map.

For odd `n`, pair the `n+1` coordinates and apply the standard quarter-turn
map `(x₁,x₂,…) ↦ (-x₂,x₁,…)`. Prove continuity, orthogonality, unit norm, and
nonvanishing before assembling Theorem 2.28. Do not introduce a tangent-bundle
API solely for this source statement.

## Free sphere actions

Represent an action exactly by a group homomorphism
`G →* (Sⁿ ≃ₜ Sⁿ)`. It is free when every nonidentity element acts without a
fixed point. Compose the action with the sphere-homeomorphism degree character
to obtain `G →* ℤˣ`.

When `n` is positive and even, property (g) makes this character injective for
a free action. Identify `ℤˣ` with `Multiplicative (ZMod 2)` and conclude that
every nontrivial freely acting group is isomorphic to `ℤ/2`. Conversely,
construct the antipodal `ℤ/2` action and prove it free. The final theorem has
no finiteness hypothesis on `G`.

## Pinned API and prior art

The repository pins Mathlib `v4.34.1` at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Reuse:

- `Hatcher.Simplex.doubleSimplexSphereFundamentalClass`, its `IsIso` theorem,
  and `sphereHomologyIsoFromDoubleSimplex`;
- `Hatcher.Reduced.homologyIsoOfPositiveDegree` and
  `Hatcher.Reduced.homologyMap_eq_of_homotopy`;
- `AddCommGrpCat.asHom`, `AddCommGrpCat.int_hom_ext`, and integer-unit facts;
- Mathlib's stereographic projection and the existing project chart work in
  `Hatcher.Sphere.HemisphereCharts`;
- `pushout.map` and its computation lemmas for the double-simplex swap; and
- `NormedSpace.normalize`, Euclidean inner-product identities, and the group
  structure on homeomorphisms.

The pinned library contains no exact mapping-degree or local-degree API and no
exact versions of Theorem 2.28 or Proposition 2.29. A circle map called a
degree map in the fundamental-group development is unrelated. No node in
this milestone is exact Mathlib coverage.

## Fine decomposition

The source unit has sixteen formalization leaves:

1. an oriented ordinary integral homology isomorphism for positive-dimensional
   spheres;
2. the homological definition and fundamental-class characterization of
   degree;
3. identity, composition, homotopy, and homotopy-equivalence degree laws;
4. stereographic contractibility of a punctured sphere;
5. degree zero for nonsurjective sphere maps;
6. the double-simplex swap negates the ordered class;
7. coordinate sign changes and their compatibility with the double-simplex
   swap;
8. degree `-1` for arbitrary equatorial sphere reflections, with coordinate
   reflections as special cases;
9. the antipodal degree formula;
10. the fixed-point-free homotopy and degree formula;
11. tangent-field data and normalization;
12. the parity obstruction from a nonvanishing tangent field;
13. the explicit nonvanishing tangent field on an odd sphere;
14. Theorem 2.28;
15. the degree character of a sphere action; and
16. the antipodal action and Proposition 2.29.
