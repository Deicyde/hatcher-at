# Canonical space-universe lifting preserves augmented sphere chains

Complete source proposal in `Hatcher/Singular/DoubleSimplexSphere.lean`.
Remote Lean compilation, axiom and linter checks, canonical proof evidence and
independent review remain required; no completion marker is asserted.

The primary construction is `Hatcher.Sphere.sphereAugmentedSpaceLiftIso`.
Its public source and target complex types use the same explicit coefficient
object `AddCommGrpCat.of.{u} (ULift.{u} ℤ)` in `AddCommGrpCat.{u}`. The space
universe changes from zero to u. All sphere dimensions, including zero, are
covered.

Public data and computation laws are `sphereCoordinateUniverseLift`,
`sphereSimplexLift`, `sphereSimplexLift_face`,
`sphereAugmentedSpaceLiftIso_f_zero`, and `sphereAugmentedSpaceLiftIso_ι`.
The coordinate homeomorphism removes the old lift and inserts the new one.
The actual continuous-map equivalence constructs the singular-simplex lift.
Reindexing the coefficient coproducts gives the degreewise isomorphisms; the
face equations and alternating differential prove chain compatibility.
The augmentation component is the identity and preserves every vertex's
augmentation. Public types inline the actual coefficient object and the
simplex data required by the next ordered-generator leaf are public.

The source is an additive append with the existing module header and every
old declaration preserved. No effective import change is needed. The exact
accepted module/project baseline is available for later semantic comparison.
Fresh target/helper blueprint searches found no duplicate endpoint. Nine
physical package indexes are absent, so indexed library coverage is unknown.
Direct pinned source supplies the singular-chain and augmented-chain APIs.

Uncompiled elaboration risks are mixed-universe continuous-map/face
normalization, coefficient-family inference, the singular degree-object
inference of `chainComplex_hom_ext`, and augmented successor-component
reductions. These require exact remote verification before acceptance.

Remote elaboration identified the continuous-map congruence as an equivalence,
requiring no extra projection. The repaired proposal uses explicit per-face
coefficient equations for the signed sum, typed actual augmentation maps for
the vertex calculation, and a dependent match for the augmented component
family. Fresh remote compilation remains required.
