---
article_id: af_ebce9802ffc8eff0bc9ddf69
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.exists_coverDecomposition_atMostThree
---

# A homotopy admits a threefold-incidence cover decomposition

Let `H` be an endpoint-fixed homotopy of paths, and let an arbitrary indexed
family of open sets cover `X`. Given finite labeled subdivisions on the bottom
and top edges whose cells already map into their labels, subdivide the square
into finitely many labeled rectangles such that:

- each region maps under `H` into its label's cover member;
- the bottom and top rows are exactly the prescribed subdivisions; and
- at most three labeled regions meet at any vertex.

The construction is `Hatcher.VanKampen.exists_coverDecomposition_atMostThree`.
The explicit incidence bound is
`Hatcher.VanKampen.StaggeredCoverGrid.interfaceIncidentCellCount_le_three`;
`Hatcher.VanKampen.IntervalSubdivision.card_incidentCells_le_two` gives the
corresponding bound of two on the outer boundary.
For cover factorizations, `Hatcher.VanKampen.Factorization.exists_staggeredCoverGrid`
instantiates the boundary rows with the canonical factor lists.

A Lebesgue number gives uniformly small middle rectangles. Compactness gives
collars on the prescribed bottom and top cells. Two fine horizontal meshes are
then chosen to avoid the boundary vertices and each other, and alternated
between the boundary rows. Adjacent rows therefore have disjoint interior
vertex sets, which gives the three-region incidence bound. The separate sweep
node turns this geometric grid into factorization moves.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2, perturbed homotopy grid on page 45](../../../sources/hatcher-1-2.md)
