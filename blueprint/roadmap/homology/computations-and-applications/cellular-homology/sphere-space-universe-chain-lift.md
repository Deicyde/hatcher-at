---
article_id: af_72fa8d9ce5a45b5bccf4b17b
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Sphere.sphereAugmentedSpaceLiftIso, Hatcher.Sphere.sphereCoordinateUniverseLift, Hatcher.Sphere.sphereSimplexLift, Hatcher.Sphere.sphereSimplexLift_face, Hatcher.Sphere.sphereAugmentedSpaceLiftIso_f_zero, Hatcher.Sphere.sphereAugmentedSpaceLiftIso_ι
---

# Canonical space-universe lifting preserves augmented sphere chains

For every universe u and sphere dimension d ≥ 0, keep the coefficient object
Rᵤ = ULiftᵤ ℤ in the category of abelian groups of universe u. Construct an
isomorphism from the augmented singular chain complex of the universe-zero
standard d-sphere to that of the same standard sphere in universe u, both
with coefficients Rᵤ.

Use the canonical coordinate homeomorphism that removes the old universe
lift and inserts the new one. Construct its induced equivalence on actual
singular simplices in every degree. The chain isomorphism must send the
coefficient-copy inclusion of each singular simplex to the inclusion of that
simplex followed by this coordinate homeomorphism. Its augmentation-degree
component is the identity of Rᵤ. Include these as explicit computation laws.

This is a change of the space model's universe with the coefficient category
fixed. The maps and their compatibility with faces and augmentation are
constructed here; no chain isomorphism, simplex equivalence, or compatibility
certificate is a premise. The result includes d = 0.

## Proof sketch

Identify each singular simplex with a continuous map from the fixed standard
real simplex, then postcompose with the canonical coordinate homeomorphism.
Postcomposition commutes with every face restriction. Reindex the actual
degreewise coproducts of coefficient copies along these equivalences and use
the alternating face formula to prove differential compatibility.

In augmentation degree zero use the identity of the coefficient object.
Every vertex generator has augmentation one, so the same component laws prove
augmentation compatibility. Assemble the degreewise isomorphisms into the
actual augmented chain isomorphism and retain the simplex-inclusion laws.

## Depends on

- [The augmented singular chain complex](../../simplicial-and-singular/relative-homology/augmented-singular-chain-complex.md)

## Proof depends on

- [The singular chain complex](../../simplicial-and-singular/singular-chain-complex.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification: sphere space-universe lift](../../../../sources/cellular-homology-implementation.md#sphere-space-universe-lift)
