# Sphere-homology implementation specification

This is a project-authored implementation specification for the selected
reduced-homology and sphere material in Hatcher §§2.1–2.2. It is not an
independent mathematical source. The cited statements come from the official
Hatcher PDF at the locations recorded in the
[§2.1 source note](hatcher-2-1.md) and
[§2.2 source note](hatcher-2-2.md).

## Mathematical scope

The milestone has two source-facing parts.

First, formalize the neighborhood-deformation-retract version of the ordinary
and reduced Mayer–Vietoris sequences from printed page 150. The theorem takes
subspaces `A`, `B`, neighborhoods `U`, `V`, and deformation-retraction data as
hypotheses. It preserves the inclusion-induced intersection and union maps; it
does not merely define arbitrary conjugates for which exactness happens to
hold.

Second, formalize the sphere recurrence in Example 2.46 and use it to recover
Corollary 2.14. For a coefficient object `R`, the successor-indexed recurrence
is

`H̃_{i+1}(S^{n+1};R) ≅ H̃_i(S^n;R)`.

The recurrence leaf also proves the vanishing of reduced zeroth homology for
positive-dimensional spheres from the terminal reduced Mayer–Vietoris
sequence. Together with the separate `S⁰` base case, the final result supplies
an isomorphism with `R` in the diagonal degree and an `IsZero` witness in every
off-diagonal degree. An explicit integral specialization records Hatcher's
displayed statement.

## Reduced homotopy invariance

Expose reduced-homology analogues of the existing ordinary singular-homology
API:

- homotopic maps induce equal maps on reduced homology;
- a homotopy equivalence induces an isomorphism whose forward morphism is the
  map induced by its forward continuous map; and
- every contractible nonempty space has zero reduced homology in all degrees.

The augmentation-preserving chain maps and homotopies should live below both
the reduced-homology and excision developments. The private helpers in
`Hatcher/Excision/AugmentedSmallChains.lean` are implementation prior art, not
a public dependency to import back into `Hatcher/Singular/Reduced.lean`.
The contractible-space theorem may use `ContractibleSpace.hequiv_unit` and the
existing reduced homology calculation for a point.

## Neighborhood data and transport

Package the hypotheses once as a structure
`Hatcher.MayerVietoris.NeighborhoodCover (A B : Set X)` whose fields include
the neighborhoods `U V : Set X`. The data records

- `A ∪ B = Set.univ`;
- `A ⊆ interior U` and `B ⊆ interior V`, hence an interior cover by `U,V`;
- strong deformation retractions from `U` to `A` and from `V` to `B`; and
- a strong deformation retraction from `U ∩ V` to `A ∩ B`, all represented by
  the actual subtype inclusions.

The ordinary and reduced sequences should be stated using the homology of
`A ∩ B`, `A`, `B`, and `X`. Transport exactness from the already formalized
binary-cover sequences for `U,V`. Include direct-formula or naturality lemmas
showing that the transported intersection and union maps are the maps induced
by the original inclusions, with Hatcher's sign convention. The reduced
degree-zero endpoint continues to require `Nonempty (A ∩ B)`.

For a strong deformation retract of `A` inside `U`, the existing
`toHomotopyEquiv` points from ambient `U` to retract `A`. The homology
isomorphism induced by the actual inclusion `A ⟶ U` must therefore be built
from `sdr.toHomotopyEquiv.symm`, using the public forward-map lemma to identify
its morphism. The reduced transport node also owns public signed-lift and
`biprod.desc` formulas for the existing `reducedIntersectionMap` and
`reducedUnionMap`, whose current implementations pass through private
augmented-chain helpers.

`Hatcher.StrongDeformationRetract` and its elementary consequences live in the
neutral module `Hatcher/Topology/StrongDeformationRetract.lean`. The existing
declaration now has a promoted, complete background roadmap owner shared by
the neighborhood-transport and good-pair branches; the ordinary transport node
no longer owns that declaration.

## Sphere model and geometry

Public results use Mathlib's universe-polymorphic `TopCat.sphere n`, which is
definitionally `TopCat.diskBoundary (n + 1)` and hence an `ULift` of the unit
metric sphere. Point-set geometry may be proved on
`Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1`, but it must cross the
lift through a single explicit homeomorphism rather than expose a competing
public sphere API.

Use Hatcher's closed northern and southern hemispheres in
`TopCat.sphere (n + 1)`, defined by the last coordinate being respectively
nonnegative and nonpositive, with poles `±e_last` and equator given by last
coordinate zero. Their interiors do not cover the equator, so they must not be
passed directly to `Hatcher.Excision.CoverCondition`. Take `U` and `V` to be
the complements of the opposite poles. The stereographic charts from the
deleted south and north poles identify each corresponding hemisphere with
`Metric.closedBall 0 2`, and identify the equator in `U ∩ V` with
`Metric.sphere 0 2` in punctured Euclidean space. Radial strong deformation
retractions give the three required neighborhood witnesses. This is the
literal hemisphere route of Example 2.46; the shorter two-puncture open-cover
proof is not the selected implementation.

The sphere geometry should be split into reusable radial retractions, the
stereographic hemisphere/equator chart package, and the final
neighborhood-cover witness. Existing private declarations in
`Hatcher/Sphere/SimplyConnected.lean` and `Hatcher/Euclidean/Dimension.lean`
are useful local prior art, but they are not yet public contracts.

## The zero-sphere base case

Construct an explicit homeomorphism between `TopCat.sphere 0` and a lifted
two-point space, together with
`∐ (_ : ULift Bool), R ≅ R ⊞ R`. Identify reduced zeroth homology with the
kernel of the induced ordinary-`H₀` augmentation, identify that augmentation
with the codiagonal under these isomorphisms, and identify its kernel with the
antidiagonal copy of `R`. This yields
`H̃_0(S⁰;R) ≅ R`; positive reduced homology vanishes by the ordinary
totally-disconnected calculation and the positive-degree comparison.

Do not infer the base case by cancellation from
`H_0(S⁰;R) ≅ R ⊞ R` and `H_0 ≅ H̃_0 ⊞ R`: cancellation is not valid in an
arbitrary abelian category without additional hypotheses.

## Coefficients and indices

Reusable results retain the coefficient-general assumptions of the existing
Mayer–Vietoris API: an abelian target category with the required coproducts and
a coefficient object `R`. Hatcher's integral groups are obtained by taking
`C = AddCommGrpCat` and `R = AddCommGrpCat.of ℤ`.

Keep the topological dimension `n` and homological degree `i` separate. State
the recurrence with successors rather than subtraction. A diagonal
isomorphism is returned under `Nonempty` so the result does not silently choose
an orientation; an orientation and homological degree API belong to the later
degree milestone.

## Intended public contract

The fine roadmap targets these main artifacts, with supporting definitions and
simp lemmas kept in the same review unit as the result they serve:

1. `Hatcher.Reduced.homologyMap_eq_of_homotopy`;
2. `Hatcher.Reduced.homologyIsoOfHomotopyEquiv`;
3. `Hatcher.Reduced.isZero_homology_of_contractible`;
4. `Hatcher.MayerVietoris.neighborhoodSequence_exact`;
5. `Hatcher.MayerVietoris.reducedNeighborhoodLongExact`;
6. `Hatcher.Sphere.closedBallStrongDeformationRetract`;
7. `Hatcher.Sphere.spherePuncturedStrongDeformationRetract`;
8. `Hatcher.Sphere.hemisphereChartData`;
9. `Hatcher.Sphere.hemisphereNeighborhoodCover`;
10. `Hatcher.Sphere.reducedHomology_sphereSucc`;
11. `Hatcher.Sphere.zeroSphereIsoTwoPoint`;
12. `Hatcher.Sphere.reducedHomology_sphere_zero`; and
13. `Hatcher.Sphere.reducedHomology_sphere`, with an integral specialization.

Exact helper names may follow the surrounding namespace conventions, but these
thirteen semantic completion targets and their separation are fixed. The
promoted strong-deformation-retract background article is not a fourteenth
source-facing sphere target.

## Pinned API and prior art

The repository pins Mathlib `v4.34.1` at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Relevant exact APIs include
`TopCat.sphere`, `TopCat.uliftFunctorObjHomeo`, `stereographic'` and its
source/target lemmas, `homeomorphSphereProd`,
`TopCat.singularHomology₀Iso`, and
`isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`. Local support
includes the completed ordinary and reduced Mayer–Vietoris sequences,
`Hatcher.Singular.homologyIsoOfHomotopyEquiv`, and
`Hatcher.StrongDeformationRetract.toHomotopyEquiv`.

Targeted GitHub searches found no Mathlib pull request or issue implementing
sphere singular homology or this neighborhood Mayer–Vietoris theorem. The
TauCeti Mayer–Vietoris work recorded in the earlier implementation
specification supplies sequence-level prior art but not the sphere calculation.
No new node is marked `mathlib: true`.

## Explicit exclusions

This sphere-calculation slice excludes Theorem 2.13 and Proposition 2.22, the
general CW `Nε(A)` construction from Appendix Proposition A.5,
Mayer–Vietoris naturality as a separate API, Examples 2.47–2.48, relative
Mayer–Vietoris, mapping cylinders and tori, degree and orientation theory,
cellular homology, and homology with general coefficient groups as a separate
source topic. Corollary 2.15 and Brouwer's theorem are selected separately in
the [Corollary 2.15 implementation specification](corollary-2-15-implementation.md).
