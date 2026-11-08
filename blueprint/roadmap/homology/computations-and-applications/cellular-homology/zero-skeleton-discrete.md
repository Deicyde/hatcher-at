---
article_id: af_d7de7378b694809a2a726f47
declaration: def
origin: bridged
---

# The zero skeleton is the discrete space of its cells

For every classical CW complex X, construct a homeomorphism from its actual
zero-cell index, equipped with the discrete topology, to X⁰. It sends each
cell to the point given by that cell’s characteristic map. The construction
includes the empty complex and arbitrarily many zero cells.

## Proof sketch

Use the successor-skeleton quotient at dimension zero. Its old skeleton and
cell boundaries are empty, and each closed zero-cell is one point. Cell
interiors are disjoint, so the characteristic points give a bijection; the
quotient topology identifies the zero skeleton with their discrete coproduct.

## Depends on

None beyond the pinned classical CW structure.

## Proof depends on

- [Successor skeleton quotient](../../../appendix/classical-cw-bridge/successor-skeleton-quotient.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)
