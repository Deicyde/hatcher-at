---
article_id: af_4c3c37a7ddc05af3eb57338c
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.ConeAttachment.lowerStrongDeformationRetract
---

# The base-side cone cover retracts onto the original space

For a continuous attaching map `f : S → X`, the open member consisting of the
canonical image of `X` together with the positive-height cone points strongly
deformation-retracts onto `X`.

Formalized as
`Hatcher.VanKampen.ConeAttachment.lowerStrongDeformationRetract`. The homotopy
pushes every positive cylinder height linearly toward one, where the boundary
is glued to `X`, and fixes the image of `X` throughout. The module also exposes
the inclusion and retraction maps and proves their composite is the identity.

## Depends on

- [A single cone attachment has a two-set open cover](single-cone-open-cover.md)

## Sources

- [Hatcher §1.2, proof of Proposition 1.26 on pages 50–51](../../../../sources/hatcher-1-2.md)
