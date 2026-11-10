# Canonical space-universe lifting preserves augmented sphere chains

Uncompiled source proposal. No statement or proof completion is asserted.

## Proposed public interface

Primary construction: `Hatcher.Sphere.sphereAugmentedSpaceLiftIso d`.
Keep all source and target complexes in `ChainComplex AddCommGrpCat.{u} ℕ`
with the same explicit coefficient object `AddCommGrpCat.of.{u} (ULift.{u} ℤ)`.
The space-functor universes are zero on the source and u on the target.

Required public data and computation declarations:

- `Hatcher.Sphere.sphereCoordinateUniverseLift d`: the actual raw-coordinate
  homeomorphism between the two sphere models.
- `Hatcher.Sphere.sphereSimplexLift d r`: the actual singular-simplex
  equivalence induced by that homeomorphism in degree r.
- `Hatcher.Sphere.sphereSimplexLift_face`: the face compatibility law.
- `Hatcher.Sphere.sphereAugmentedSpaceLiftIso_f_zero`: identity of the actual
  coefficient object in augmentation degree zero.
- `Hatcher.Sphere.sphereAugmentedSpaceLiftIso_ι`: each coefficient-copy
  inclusion maps to the inclusion indexed by `sphereSimplexLift d r s`.

The simplex equivalence is public because the next bridge's literal first and
second simplex definitions and difference equation need that actual map.
Public statement types must use these public data or inline the actual
objects, rather than refer to inaccessible private aliases.

## Implementation route

Use `TopCat.toSSetObjEquiv` and `Homeomorph.continuousMapCongr` for the
canonical space lift. Reindex the coefficient coproducts with
`Sigma.whiskerEquiv`, prove the alternating differential law by
`SSet.ιChainComplex_d`, and extend to augmentation degree zero by the identity.
`Hatcher.Reduced.ι_chainAugmentation` fixes the augmentation equation.
`HomologicalComplex.Hom.isoOfComponents` assembles the actual isomorphism.

The prepared complete draft isolates this chain-lift block from the ordered
generator block. Likely existing source location is
`Hatcher/Singular/DoubleSimplexSphere.lean`, whose closure already supplies the
underlying reduced chains and sphere model. Effective imports and ownership
must be checked from the exact accepted baseline before source edits.

Direct pinned Mathlib and source-bound blueprint searches found no duplicate
endpoint with these actual simplex and augmentation equations. Nine package
indexes are unavailable, so indexed coverage is unknown. Mixed-universe
simplex face normalization, copied coefficient instances and the augmented
component reductions remain uncompiled risks. Exact Lean builds, axiom and
linter checks, full evidence and independent review are required.
