---
article_id: af_a49559529154d01853bcde2e
---

# Cell-attachment support

These nodes isolate the reusable algebra, elementary circle geometry, and the
first point-set construction around Hatcher's cell-attachment applications.

## Point-set geometry

- [A single cone attachment has a two-set open cover](single-cone-open-cover.md)
- [An indexed family of cones has a two-set open cover](indexed-cone-open-cover.md)
- [The base-side cone cover retracts onto the original space](single-cone-base-retract.md)
- [The cone-side cover member is contractible](single-cone-upper-contractible.md)
- [The single-cone cover intersection has the homotopy type of its boundary](single-cone-intersection.md)
- [The cone on a disk boundary is the disk](cone-disk-homeomorphism.md)
- [A single cone attachment is a topological pushout](single-cone-pushout.md)
- [A single cone attachment is a standard cell attachment](single-basic-cell-attachment.md)
- [An indexed family of cone attachments is a topological pushout](indexed-cone-pushout.md)
- [An indexed cone attachment is a standard cell attachment](indexed-basic-cell-attachment.md)
- [Every abstract cell attachment has an indexed cone model](abstract-cell-attachment-indexed-model.md)
- [An attachment with no cells is an isomorphism](empty-cell-attachment-iso.md)

The raw indexed quotient has one apex per cell, so its upper member is generally
disconnected. Hatcher repairs this by adjoining a shared spine and one strip per
cell. The strip-enlarged point-set construction is organized in
[Hatcher's auxiliary cell-attachment cover](auxiliary/README.md). The separate
[two-disk boundary comparison](disk-boundary-two-circle.md) fixes the circle
parameterization used by the two-cell relation calculation.

The finite-stage constructors, pointed-wedge interfaces, and relator family
needed for Corollary 1.28 are decomposed in
[presentation-complex support](../presentation-complex/README.md).

## Binary-cover algebra

- [A binary cover with a trivial second fundamental group](binary-cover-trivial-piece-quotient.md)
- [A binary cover with a contractible second piece](binary-cover-contractible-piece.md)

## Circle input

- [The circle is well-pointed at one](circle-well-pointed.md)
- [The degree-n circle map sends the generator to the degree-n loop](circle-degree-map.md)
- [The degree-n circle relation gives the cyclic group](cyclic-relation-quotient.md)

The family open-cover construction and attaching-sphere analysis are packaged
in the parent [Van Kampen roadmap](../README.md), where they feed the
now-formalized 2-cell and higher-cell attachment theorems.
