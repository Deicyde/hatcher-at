# Signed sphere fold

## Canonical construction

`Hatcher.Sphere.signedSphereFoldMap n hn k σ hσ` constructs
`SignedSphereFoldData (sphereBallPinch n hn k) σ`, for
`σ : Fin k → ℤ` and `hσ : ∀ i, σ i = 1 ∨ σ i = -1`.
The certificate contains the actual continuous based fold, its point and
summand equations, and the derived corrected-component degree equations.
Its `selfMap` is definitionally the fold composed with the actual pinch.

The correction `SphereBallPinchData.signedCorrectionIso` is the identity
when the actual `degree` of `componentCollapse i` equals `σ i`, and the
existing `coordinateReflectionIso n 0` otherwise. It supplies the actual
inverse as well as the continuous hom. The canonical constructor's input
contains the prescribed sign family; degree equations are proved as output
certificates for these fixed maps.

## Basepoint and degree proofs

`zeroth_reflection_apply_basepoint` uses
`reflectionIso_coordinateNormal` and the existing `sphereULiftHomeomorph`
comparison to reduce the actual coordinate reflection at `D.b` to exactly
`D.zeroth_reflection`. The sphere and reflection models are the existing
project models.

`signed_corrected_component_degree` uses the actual component unit theorem,
`degree_comp`, `degree_id`, and `degree_coordinateReflection`. Categorical
corrected composition is the component followed by its selected correction.
The four possible unit/sign pairs prove the requested signed integer.

`basedSignedFold` is `PointedWedge.desc` of the corrections with their
proved common basepoint. The private `signed_sphere_fold_data_nonempty`
theorem constructs the complete certificate before the canonical choice.
Its degree equations follow from the actual maps and computed units.

## Computations and verification

`SignedSphereFoldData.self_map_apply_ball` gives agreement with the corrected
actual component on each literal open ball. `self_map_apply_compl` and
`self_map_apply_basepoint` give the common point elsewhere and at `D.b`.
`self_map_zero` identifies the empty-family self-map with the actual constant
map. No positive-cardinality or chart-orientation premise is introduced.

The full proposed source requires remote compilation, including the reflection
normalization, iso/hom/continuous-map coercions, signed degree cases,
certificate elaboration/extraction, and point/ball/empty-family computations.
The existing import closure supplies the reached APIs. Full validation and
independent review remain pending.


## Useful failed route and current repair

The first remote focused build could not rewrite categorical degree
multiplicativity after unfolding the correction inline: implicit transparency
left a mismatch between the bundled TopCat sphere topology and its reduced
raw representation. The replacement fixes the component as an explicitly
typed TopCat morphism, proves the selected correction isomorphism equation,
and invokes degree_comp with explicit morphism arguments. Public statements,
inputs, original source and CI selectors are preserved. Current if-branch
lemmas replace deprecated names. Exact compilation remains required.
