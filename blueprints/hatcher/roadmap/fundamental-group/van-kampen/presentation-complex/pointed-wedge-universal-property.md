---
article_id: af_35e455c0951614a9498ecf00
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.PointedWedge.continuousMapEquiv
---

# Continuous maps out of a pointed wedge

Package the universal property of `Hatcher.PointedWedge`: a continuous map
from the wedge is equivalent to a target point together with continuous maps
from every summand that send its chosen basepoint to that target point.

Also expose a constructor `desc`, simp lemmas for the wedge point and each
inclusion, an extensionality theorem, and a homeomorphism constructor
`Hatcher.PointedWedge.homeomorphCongr` for basepoint-preserving families of
summand homeomorphisms. The construction must include the empty-index case.

## Depends on

- [The pointed wedge of a family of spaces](../pointed-wedge.md)

## Sources

- [Hatcher §1.2, Example 1.21 and the adopted wedge representation](../../../../sources/hatcher-1-2.md)
- [Presentation-complex implementation specification](../../../../sources/presentation-complex-implementation.md)
