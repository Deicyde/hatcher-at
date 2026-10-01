---
article_id: af_3810514880894eb04f67c787
source_units: [hatcher-2-2-mv-transport-sphere-recurrence]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Sphere.hemisphereNeighborhoodCover
---

# The hemispheres have compatible neighborhood deformation retractions

For every `n`, equip the northern and southern hemispheres of
`TopCat.sphere (n + 1)` with the punctured-pole neighborhoods from the
stereographic model. Transport the radial deformation retractions through the
charts to obtain strong deformation retractions of each neighborhood onto its
hemisphere and of their intersection onto the equator.

The main artifact
`Hatcher.Sphere.hemisphereNeighborhoodCover n` is a
`Hatcher.MayerVietoris.NeighborhoodCover` for the two closed hemispheres. It
also exposes a nonempty point of the equator, needed by the terminal reduced
sequence. The package must use the literal closed hemispheres of Example 2.46;
it must not replace them silently by an antipodal-complement open cover.

## Depends on

- [The ordinary neighborhood-retract Mayer–Vietoris sequence](ordinary-neighborhood-mayer-vietoris.md)
- [Stereographic models for hemispheres and the equator](sphere-hemisphere-stereographic-models.md)

## Proof depends on

- [A closed ball strongly deformation retracts from Euclidean space](closed-ball-radial-deformation-retract.md)
- [A sphere strongly deformation retracts from punctured Euclidean space](punctured-space-radial-deformation-retract.md)

## Sources

- [Hatcher §2.2, Example 2.46, page 150](../../../../sources/hatcher-2-2.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
