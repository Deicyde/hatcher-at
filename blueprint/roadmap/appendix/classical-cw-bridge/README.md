---
article_id: af_4ad90cefabf555feada62a5d
---

# Classical CW bridge support

Mathlib has two CW-complex APIs: characteristic maps and skeleta in the
classical point-set API, and categorical cell attachments in the abstract API.
These nodes build only the successor-stage bridge required by Hatcher's
Proposition 1.26(c).

## Cell-attachment bridge

- [Classical and standard cells have isomorphic attaching arrows](classical-cell-arrow-iso.md)
- [A successor classical skeleton has the cell-attachment quotient topology](successor-skeleton-quotient.md)
- [Classical skeleton inclusions are abstract cell attachments](../classical-skeleton-cell-attachment.md)

## Compactness and connectivity

- [Compact subsets lie in a bounded skeleton](compact-subset-bounded-skeleton.md)
- [The 2-skeleton of a path-connected CW complex is path-connected](../../fundamental-group/van-kampen/cell-attachment-support/path-connected-two-skeleton.md)

The exact conventions and upstream status are recorded in the
[project-authored implementation specification](../../../sources/classical-abstract-cw-bridge.md).
