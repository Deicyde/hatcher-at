---
article_id: af_e9e884c0b3be617ff7d221dc
source_units: [hatcher-2-2-mv-transport-sphere-recurrence]
declaration: def
origin: bridged
---

# Stereographic models for hemispheres and the equator

For `TopCat.sphere (n + 1)`, define the closed northern hemisphere, closed
southern hemisphere, equator, north and south poles, and the two neighborhoods
obtained by deleting the opposite poles. Bridge Mathlib's `ULift`-based
`TopCat.sphere` once to the corresponding unit `Metric.sphere` so all public
objects remain universe-polymorphic.

The main artifact `Hatcher.Sphere.hemisphereChartData n` packages
the last-coordinate hemispheres, the poles `±e_last`, and the neighborhoods
given by their opposite-pole complements. Its stereographic homeomorphisms
identify a hemisphere inside its neighborhood with
`Metric.closedBall 0 2` inside Euclidean space and the equator inside the
overlap with `Metric.sphere 0 2` inside punctured Euclidean space. It also
records that the two hemispheres cover the sphere, their intersection is the
equator, and the equator is homeomorphic to `TopCat.sphere n`. Include the
commuting inclusion squares needed to transport strong deformation retractions
back through these charts.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §2.2, Example 2.46, page 150](../../../../sources/hatcher-2-2.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
