# Good-pair quotient implementation specification

This is a project-authored implementation specification for Hatcher §2.1,
Theorem 2.13 and Proposition 2.22. It is not an independent mathematical
source. The mathematical statements are in the official Hatcher text at the
locations recorded in the [§2.1 source note](hatcher-2-1.md).

## Mathematical scope

For a good pair `(X,A)`, formalize:

- Proposition 2.22: the quotient map induces
  `H_n(X,A;R) ≅ H_n(X/A,A/A;R) ≅ H̃_n(X/A;R)` in every degree;
- Theorem 2.13: the reduced long exact sequence
  `⋯ → H̃_n(A;R) → H̃_n(X;R) → H̃_n(X/A;R) → H̃_{n-1}(A;R) → ⋯`,
  including the terminal map `H̃_0(X/A;R) → 0`; and
- the naturality asserted on printed page 128 for arbitrary maps of good
  pairs and their induced quotient maps.

Hatcher defines a good pair on printed page 114 as a nonempty closed subspace
`A ⊆ X` that is a deformation retract of some neighborhood in `X`.
Proposition 2.22 and its proof are entirely on printed page 124. Theorem 2.13
is stated on page 114, and its naturality is stated on page 128.

The arbitrary-pair mapping-cone comparison following Proposition 2.22,
Example 2.17, Example 2.23 and Corollaries 2.24–2.25, and the assertion that
nonempty CW subcomplex pairs are good by Appendix Proposition A.5 are not in
this milestone.

## Good pairs

Use a topological pair `P : TopPair`, so its subspace is represented by the
embedding `P.map : P.snd ⟶ P.fst`. Define chosen proof data
`Hatcher.Relative.GoodPairData P` containing:

- `Nonempty P.snd`;
- closedness of `Set.range P.map`;
- a set `V : Set P.fst` with
  `Set.range P.map ⊆ interior V`; and
- a `Hatcher.StrongDeformationRetract` for the induced embedding
  `P.snd → V`.

This records Hatcher's literal neighborhood hypothesis. Do **not** require
`IsOpen V`: that would be a genuine strengthening of the source. Define the
property `Hatcher.Relative.IsGoodPair P := Nonempty (GoodPairData P)` and the
full subcategory of good pairs. Morphisms in that subcategory are ordinary
maps of pairs; they do not preserve chosen neighborhoods or deformation
retractions.

## Functorial point quotients

For every topological pair, represent `X/A` by the pushout in `TopCat`

`X ⊔_A PUnit`,

where the second map is the unique map `A → PUnit`. The pushout inclusion of
`PUnit` is the collapsed point. Package the point inclusion as a topological
pair and obtain a functor

`Hatcher.Relative.pointQuotientPairFunctor : TopPair ⥤ TopPair`

together with the natural comparison

`Hatcher.Relative.pointQuotientComparison : 𝟭 TopPair ⟶ pointQuotientPairFunctor`.

The quotient pair must agree canonically with the existing
`Hatcher.Relative.pointedPair` model. Functoriality is defined for every map
of pairs before restricting to good pairs; this is the basis for the
source-facing naturality theorem.

The topology layer must prove that the ambient projection is a quotient map,
identify the fibre of the collapsed point, and construct the homeomorphism
between the two complements. For good-pair data, put `qV := q '' V`. Prove
`q ⁻¹' qV = V`, that the restricted map `V → qV` is a quotient map even when
`V` is not open, and that the collapsed point lies in `interior qV`. Descend
the chosen deformation through this restricted quotient map to contract `qV`
to the collapsed point.

## Proposition 2.22

Follow Hatcher's printed-page-124 diagram:

`H_n(X,A) → H_n(X,V) ← H_n(X ∖ A,V ∖ A)`

maps vertically under the quotient to

`H_n(X/A,A/A) → H_n(X/A,V/A) ←`
`H_n((X/A) ∖ (A/A),(V/A) ∖ (A/A))`.

The two left horizontal maps are isomorphisms because `V` retracts to `A`
and `V/A` retracts to `A/A`. The two right horizontal maps are the completed
deleted-subset excision maps. The right vertical map is induced by the
homeomorphism off the collapsed subspace. Package the canonical squares and
prove the left quotient comparison is an isomorphism.

Use the pinned
`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃` to obtain relative
homology isomorphisms from isomorphisms on both components, explicitly
including degree zero. Compose the canonical quotient comparison with
`Hatcher.Relative.pointedPairHomologyIso` to define

`α_n : H_n(X,A;R) ≅ H̃_n(X/A;R)`.

Its forward map must be exactly the quotient-induced relative map followed by
the existing pointed comparison.

## Theorem 2.13 and naturality

Transport the completed reduced pair sequence through `α_n`. Define the
displayed map `H̃_n(X) → H̃_n(X/A)` to be the canonical map induced by the
ambient quotient `q : X → X/A`, and prove it agrees with the transported map;
an unspecified conjugate is weaker than Hatcher's theorem. Include every
adjacent six-term exact window, overlap lemmas, the terminal degree-zero
sequence, and their long-exact package.

First prove naturality of `pointedPairHomologyIso` for based maps in every
degree, including the degree-zero endpoint. Then package `α_n` as a natural
isomorphism on the full good-pair subcategory and prove

`reducedPairProjection ≫ α_n.hom = H̃_n(q)`.

The final naturality theorem applies to every map of good pairs. It includes
the connecting square, overlap compatibility, and the terminal degree-zero
square without requiring any preservation of chosen witness data.

## Coefficients and indexing

State the reusable API for a coefficient object `R` in an abelian category
with the coproducts required by singular chains, following the existing
relative and reduced homology APIs. Hatcher's integral groups are the
specialization to `AddCommGrpCat.of ℤ`. Use adjacent natural-number degrees
`m + 1 = n`, and retain a separate degree-zero endpoint.

## Pinned boundary and prior art

The repository pins Mathlib `v4.34.1` at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. It contains `TopPair`, all
small-chain and excision prerequisites used locally, the generic homology
sequence, and TopCat colimits. It has no exact good-pair, NDR-pair,
point-quotient comparison, Proposition 2.22, or Theorem 2.13 declaration.
Mathlib's abstract model-category `Cofibration` has no `TopCat` instance and is
not the representation for this milestone. No new node is `mathlib: true`.

The private `fairinternal/formal-math` repository at commit
`c05951e057a5974564d67b91c9c7ec3c9a415fac` contains sorry-free prior art for
the same pushout architecture and an abstract Eilenberg–Steenrod comparison.
It is implementation prior art, not a dependency or mathematical source.
Its topology design may be independently adapted under project namespaces,
but helpers whose files lack explicit license headers must be reimplemented,
not copied.

## Fine decomposition

The milestone has fifteen formalization leaves:

1. good-pair witness data;
2. the functorial point quotient and natural comparison;
3. quotient projection, fibre, closed point, and complement topology;
4. restriction to a source-exact good-pair neighborhood;
5. contraction of the quotient neighborhood;
6. the complementary excision diagram;
7. a componentwise relative-homology isomorphism criterion;
8. the original neighborhood relative-homology isomorphism;
9. the quotient-neighborhood relative-homology isomorphism;
10. the complement comparison isomorphism;
11. Proposition 2.22 and the relative-to-reduced comparison;
12. naturality of the pointed relative-to-reduced comparison;
13. naturality of the good-pair quotient comparison;
14. Theorem 2.13 with its degree-zero endpoint; and
15. naturality of the quotient exact sequence.
