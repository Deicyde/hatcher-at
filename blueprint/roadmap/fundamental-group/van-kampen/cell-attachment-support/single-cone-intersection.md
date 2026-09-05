---
article_id: af_583d33f600e077d48f72815a
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.ConeAttachment.coverIntersectionHomotopyEquivBase
---

# The single-cone cover intersection has the homotopy type of its boundary

For the standard two-set cover of a single cone attachment, the intersection
is homeomorphic to the open cylinder `S × (0,1)` and hence homotopy equivalent
to the attaching space `S`.

The homeomorphism is
`Hatcher.VanKampen.ConeAttachment.interiorCylinderHomeomorphCoverIntersection`;
the source-facing homotopy equivalence is
`Hatcher.VanKampen.ConeAttachment.coverIntersectionHomotopyEquivBase`. The
proof restricts the quotient map to the open intersection and observes that no
endpoint identifications remain there.

No continuity hypothesis on the attaching function is needed for this
identification. Continuity enters when the cover pieces are compared with the
base space and the full attachment pushout.

## Depends on

- [A single cone attachment has a two-set open cover](single-cone-open-cover.md)

## Sources

- [Hatcher §1.2, proof of Proposition 1.26 on pages 50–51](../../../../sources/hatcher-1-2.md)
