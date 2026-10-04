# Post-excision applications implementation specification

This is a project-authored implementation specification for the applications
immediately following Hatcher's proof of excision in §2.1. It is not an
independent mathematical source. The cited statements and proofs are in the
official Hatcher text at the locations recorded in the
[§2.1 source note](hatcher-2-1.md).

## Mathematical scope

Formalize the following material from printed pages 125–126:

- the arbitrary-pair comparison
  `H_n(X,A;R) ≅ H̃_n(X ∪ CA;R)` with the topological mapping cone of
  `A → X`;
- Example 2.23's named relative fundamental cycle for the standard simplex
  and ordered difference cycle for the sphere;
- Corollary 2.24, excision for a CW complex written as the union of two
  subcomplexes;
- Corollary 2.25, additivity of reduced homology over a pointed wedge; and
- Theorem 2.26 for homeomorphic nonempty open subsets of Euclidean spaces.

Stop before Theorem 2.27. Degree, cellular homology, homology with
coefficients as a separate source topic, the simplicial–singular comparison,
and invariance of domain are not part of this milestone.

## Mapping cones

Represent `X ∪ CA` by the existing explicit quotient
`Hatcher.VanKampen.ConeAttachment P.map` for `P : TopPair`. Its height-zero
end is the cone apex and its height-one end is attached to `X`, matching
Hatcher's convention.

Use the existing lower and upper open cover rather than introducing a second
literal cone-subspace API. The lower member deformation retracts to `X`, the
upper member is contractible, and their intersection has the homotopy type of
`A`. Binary-cover excision compares the relative homology of this cover pair
with the mapping cone relative to its upper member. The reduced pair sequence
for a contractible subspace then gives Hatcher's comparison in every degree,
including the empty-`A` case supplied by the model's explicit apex.

The final isomorphism must expose the canonical composite of the cover
retraction, excision map, and reduced-pair projection. No functorial
mapping-cone category or naturality theorem is required by this source slice.

## Explicit fundamental cycles

Work integrally for Hatcher's source-facing orientation statements, while
allowing a coefficient object `R` in reusable intermediate declarations when
the same proof is valid. A fundamental class is a named morphism

`R ⟶ H_n(-;R)`

proved to be an isomorphism. An arbitrary chosen isomorphism or the existing
unoriented `Nonempty (H̃_n(S^n;R) ≅ R)` does not identify Hatcher's cycle and
is not a completion of Example 2.23.

For the standard simplex, use the universal identity singular simplex. Omit
face zero in the horn induction, so the connecting morphism sends the identity
class to the lower-dimensional identity class with coefficient `+1`. Prove
the needed connecting-map formula at the cycle level; do not use the
simplicial–singular comparison theorem, which is the later Theorem 2.27.

For the sphere, construct the ordered double-simplex model with the two
boundaries identified preserving vertex order. Its named cycle is the first
top simplex minus the second. Prove that this class is a generator before
transporting it across a homeomorphism to `TopCat.sphere n`. Keep the ordered
model and transported cycle in the public contract; do not claim that it is
definitionally the unoriented sphere isomorphism already in the project.

## CW-subcomplex excision

Use the fixed-radius regular-neighborhood system specified in
[the Appendix A.5 implementation note](cw-subcomplex-neighborhood-implementation.md).
For subcomplexes `A` and `B` with ambient carrier `X = A ∪ B`, their regular
neighborhoods form an open cover, their intersection is the regular
neighborhood of `A ∩ B`, and all three neighborhoods deformation retract to
their subcomplexes. Combine binary-cover excision with the componentwise
relative-homology criterion to prove the canonical map

`H_n(B,A ∩ B;R) ⟶ H_n(X,A;R)`

is an isomorphism. This route includes `A ∩ B = ∅`; a proof solely through
the project's current nonempty `GoodPairData` would not.

## Wedge additivity

Reuse `Hatcher.PointedWedge X x₀`. Define the topological pair whose ambient
space is `Σ i, X i` and whose subspace is the sigma family of chosen
basepoints. Identify its point quotient with the existing pointed wedge.

First prove that singular and relative chain complexes of a topological sigma
are the coproducts of the summand complexes. Pass this comparison through
homology under the corresponding `AB4OfSize` hypothesis. The integral
source-facing theorem uses Mathlib's `AB4 AddCommGrpCat` instance. Do not state
arbitrary coefficient-category wedge additivity from `Abelian` and
`HasCoproducts` alone: infinite coproducts need not be exact there.

For a nonempty index type, assemble pointwise good-pair data on the sigma
pair and use Proposition 2.22. Handle the empty family separately, where the
project's wedge model is its adjoined point and has zero reduced homology. The
final map must be the coproduct of the inclusion-induced maps displayed by
Hatcher, not an unspecified abstract isomorphism.

## Local homology and invariance of dimension

Define the punctured pair `(X, X \ {x})`. If `{x}` is closed and `U` is an
open neighborhood of `x`, the canonical map from the local pair in `U` to the
local pair in `X` induces an isomorphism by the completed
deleted-subset/binary-cover excision API. State the reusable theorem with
`IsClosed {x}` and add a `T1Space` specialization. Package the induced pair
isomorphism under a homeomorphism.

For a contractible ambient space, extract from the reduced pair sequence the
canonical comparison

`H_{i+1}(X,A;R) ≅ H̃_i(A;R)`

and the degree-zero vanishing for nonempty `A`. Translate a puncture to the
origin, use the completed strong deformation retraction of punctured Euclidean
space onto the unit sphere, and apply the completed sphere-homology theorem.
Thus positive-dimensional Euclidean local homology is the coefficient object
in the ambient dimension and zero in every other degree.

The final dimension-detection argument specializes to integral coefficients:
the nonzero object `AddCommGrpCat.of ℤ` detects the unique local-homology
degree. Do not state the contradiction for an arbitrary coefficient object,
which could be zero.

Treat dimension zero separately. A nonempty open subset of zero-dimensional
Euclidean space is subsingleton, while a nonempty open subset in positive
dimension contains two distinct points. Do not encode the zero-dimensional
case with `Nat` subtraction or a fictitious negative sphere.

## Pinned boundary and prior art

The repository pins Mathlib `v4.34.1` at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. It has singular and relative
homology, classical CW complexes, topological colimits, and the algebraic
homology-sequence tools used here, but no exact topological mapping-cone
comparison, explicit simplex/sphere fundamental cycles, CW-subcomplex
regular-neighborhood theorem, wedge-homology theorem, or Hatcher-style local
homology/invariance-of-dimension theorem. No leaf in this milestone is
`mathlib: true`.

Mathlib PR
[#36770](https://github.com/leanprover-community/mathlib4/pull/36770) is open
and unmerged. It develops invariance of domain from a Brouwer fixed-point
hypothesis and includes an `invariance_of_dimension` theorem for whole
finite-dimensional real inner-product spaces. It is an alternative,
conditional route and does not state Hatcher's theorem for arbitrary nonempty
open subsets. It is implementation prior art only.

Targeted searches found no overlapping Mathlib issue or pull request for the
other selected results. Algebraic chain-complex mapping cones are not the
topological mapping cone used here.

## Fine decomposition

The §2.1 source unit has twenty-seven formalization leaves:

1. the topological mapping-cone model and cover pair;
2. reduced-to-relative homology for a contractible subspace;
3. the mapping-cone cover retraction on relative homology;
4. the arbitrary-pair mapping-cone comparison;
5. standard-simplex boundary, horn, and identity-simplex data;
6. the zero horn strong deformation retraction;
7. good-pair data for the simplex boundary and horn;
8. the zero-face point-quotient homeomorphism;
9. the zero-face relative-homology comparison;
10. the connecting morphism's cycle formula for a triple;
11. the relative simplex fundamental class;
12. the simplex–disk pair homeomorphism;
13. the ordered double-simplex model and difference cycle;
14. the double-simplex relative comparison;
15. the double-simplex difference class is a generator;
16. transport of the explicit class to the standard sphere;
17. CW-subcomplex excision, using the separate Appendix A.5 branch;
18. the sigma pointed pair and summand maps;
19. the singular-chain coproduct comparison for topological sigmas;
20. the relative-homology coproduct comparison under `AB4OfSize`;
21. good-pair data for a nonempty sigma of pointed pairs;
22. the point quotient of the sigma pair is the pointed wedge;
23. reduced homology of a pointed wedge;
24. open-neighborhood invariance of local homology;
25. relative homology in a contractible ambient space;
26. local homology of punctured Euclidean space; and
27. invariance of dimension for homeomorphic nonempty open subsets.
