---
article_id: af_71b0371444cb6512f02a8169
source_units: [hatcher-2-2-mv-transport-sphere-recurrence]
declaration: structure
origin: background
statement: formalized
lean: Hatcher.StrongDeformationRetract
---

# Strong deformation retracts

Package an inclusion `i : C(A,Y)`, a retraction `r : C(Y,A)`, the identity
`r ∘ i = id`, and a homotopy from `id_Y` to `i ∘ r` relative to the image of
`i` as `Hatcher.StrongDeformationRetract i`.

Expose the induced `ContinuousMap.HomotopyEquiv` and the elementary transport
of contractibility and path connectedness. This neutral topology interface is
already formalized in `Hatcher/Topology/StrongDeformationRetract.lean`; this
article gives the existing declaration its own reusable roadmap owner instead
of leaving it hidden inside the Mayer–Vietoris review unit.

## Depends on

None.

## Sources

- [Hatcher §2.2, neighborhood deformation-retract extension, page 150](../../../../../sources/hatcher-2-2.md)
- [Sphere-homology implementation specification](../../../../../sources/sphere-homology-implementation.md)
