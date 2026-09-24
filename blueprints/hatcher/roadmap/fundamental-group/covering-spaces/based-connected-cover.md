---
article_id: af_ea94d53a9ef0926ab162bfee
source_units: [hatcher-1-3-selected-spine]
declaration: structure
origin: background
statement: formalized
proof: formalized
lean: Hatcher.BasedConnectedCover
---

# Pointed connected covering spaces

Define a small, universe-indexed record `Hatcher.BasedConnectedCover X x₀`
containing:

- a total-space type with its topology;
- a projection to `X` and a proof that it is a covering map;
- a chosen point over `x₀`; and
- path-connectedness of the total space.

The same file should define basepoint-preserving covering isomorphisms as
homeomorphisms commuting with projection, unpointed connected covers, and the
corresponding isomorphism relations.

Formalized in `Hatcher/Covering/ConnectedCover.lean`. Cover isomorphisms may
relate total spaces in different universes, while the named setoid instances
remain fixed at one total-space universe for later classification quotients.

This direct record is deliberately smaller than a category inside
`TopCat.Over X`. Fix the total-space universe as an explicit parameter so the
classification theorem cannot hide a size assumption.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.3, covering isomorphisms and Theorem 1.38](../../../sources/hatcher-1-3.md)
