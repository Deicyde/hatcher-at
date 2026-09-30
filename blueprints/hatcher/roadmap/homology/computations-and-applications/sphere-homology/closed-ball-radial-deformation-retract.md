---
article_id: af_5147501f7fe804efe87f1dca
source_units: [hatcher-2-2-mv-transport-sphere-recurrence]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Sphere.closedBallStrongDeformationRetract
---

# A closed ball strongly deformation retracts from Euclidean space

Let `E` be a real normed vector space and let `r > 0`. Construct the radial
clamping retraction from `E` onto `Metric.closedBall (0 : E) r`, together with
a homotopy from the identity to inclusion after retraction that fixes every
point of the closed ball.

The main artifact is
`Hatcher.Sphere.closedBallStrongDeformationRetract`, expressed using
`Hatcher.StrongDeformationRetract` for the canonical subtype inclusion. It is
the reusable Euclidean witness needed to transport a hemisphere from its
punctured-sphere neighborhood.

## Depends on

- [The ordinary neighborhood-retract Mayer–Vietoris sequence](ordinary-neighborhood-mayer-vietoris.md)

## Sources

- [Hatcher §2.2, target hemisphere decomposition in Example 2.46](../../../../sources/hatcher-2-2.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
