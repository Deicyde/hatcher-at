---
declaration: lemma
origin: bridged
not_ready: true
---

# A homotopy admits a threefold-incidence cover decomposition

Let `F : I × I → X` be continuous and let an arbitrary indexed family of open
sets cover `X`. Given finite subdivisions prescribed on the bottom and top
edges, refine the square into finitely many labeled regions such that:

- each region maps under `F` into its label's cover member;
- the bottom and top boundaries refine the prescribed subdivisions;
- the regions admit Hatcher's ordered sweep from bottom to top; and
- at most three labeled regions meet at any vertex.

Intended artifact:
`Hatcher.VanKampen.exists_coverDecomposition_atMostThree`.

Mathlib's
`exists_monotone_Icc_subset_open_cover_unitInterval_prod_self` supplies the
initial product grid. The remaining work is Hatcher's perturbation of the
intermediate vertical sides and a Lean representation of the resulting sweep.
This node remains not ready until that finite planar data structure and its
boundary API are fixed.

A plain product grid is insufficient because four independently labelled
rectangles may meet at an interior vertex. The required replacement is a
staggered grid with strictly increasing row-specific subdivisions, prescribed
refinements on the bottom and top edges, and disjoint interior cut sets in
adjacent bands. The missing geometric lemma must deduplicate the weakly
monotone grid supplied by Mathlib and strengthen the compactness argument so
the perturbed cuts retain enough margin for every closed rectangle to remain
inside one cover preimage. With that condition, each sweep event involves at
most three labels.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2, perturbed homotopy grid on page 45](../../../sources/hatcher-1-2.md)
