---
article_id: af_bb19d99fce28cd9e2c2961bb
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.factorization_quotient_eq_of_homotopic
---

# Homotopic factorizations have the same quotient class

Let an arbitrary indexed family of open subsets cover `X`, contain a shared
basepoint, and have path-connected members, pairwise intersections, and triple
intersections. If two cover factorizations represent homotopic based loops,
then their words have the same class modulo the overlap-relation subgroup.

Intended artifact: `Hatcher.VanKampen.factorization_quotient_eq_of_homotopic`.

Follow Hatcher's sweep argument using a cover-subordinate decomposition in
which at most three regions meet at each vertex. Choose connector paths at
vertices in the resulting double or triple intersections, then compare
successive cuts by the elementary moves. A plain product grid is insufficient:
four labels can meet at an interior vertex, which would add a hypothesis absent
from Theorem 1.20.

## Depends on

- [Cover factorizations of a loop](cover-factorization.md)
- [The group presentation associated to an open cover](cover-group-presentation.md)

## Proof depends on

- [Elementary factorization moves preserve the quotient class](factorization-moves.md)
- [A homotopy admits a threefold-incidence cover decomposition](homotopy-cover-decomposition.md)

## Sources

- [Hatcher §1.2, proof of Theorem 1.20 on pages 44–46](../../../sources/hatcher-1-2.md)
