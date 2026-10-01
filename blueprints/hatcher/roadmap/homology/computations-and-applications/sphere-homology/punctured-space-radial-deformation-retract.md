---
article_id: af_ef8d3aebf368209450a69077
source_units: [hatcher-2-2-mv-transport-sphere-recurrence]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Sphere.spherePuncturedStrongDeformationRetract
---

# A sphere strongly deformation retracts from punctured Euclidean space

Let `E` be a nontrivial real normed vector space and let `r > 0`. Construct
the normalization retraction from `({0}ᶜ : Set E)` onto
`Metric.sphere (0 : E) r`, and a radial homotopy from the identity to inclusion
after retraction that fixes the radius-`r` sphere.

The main artifact is
`Hatcher.Sphere.spherePuncturedStrongDeformationRetract`, expressed using the
canonical subtype inclusion. Mathlib's `homeomorphSphereProd` is useful prior
art, but the completion criterion is the strong deformation retraction needed
by the neighborhood Mayer–Vietoris data.

## Depends on

- [The ordinary neighborhood-retract Mayer–Vietoris sequence](ordinary-neighborhood-mayer-vietoris.md)

## Sources

- [Hatcher §2.2, target equatorial decomposition in Example 2.46](../../../../sources/hatcher-2-2.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
